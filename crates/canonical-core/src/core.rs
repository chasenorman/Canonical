use thread_local_collect::tlm::channeled::Control;
use Index::*;
use crate::heuristic::next;
use crate::memory::{S, W, WVec};
use std::num::NonZero;
use std::sync::atomic::{AtomicU64, Ordering};
use string_interner::DefaultSymbol;
use std::iter;
use crate::stats::SearchInfo;
use mimalloc::MiMalloc;
use std::cell::RefCell;
use std::ops::{ControlFlow, Range};
use core::slice::Iter;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

/// Used to give each hardware thread a unique ID.
static THREAD_COUNTER: AtomicU64 = AtomicU64::new(0);

thread_local! {
    /// Each thread generates a disjoint set of `u64`s, starting from the hardware thread ID.
    static COUNTER: RefCell<u64> = RefCell::new(THREAD_COUNTER.fetch_add(1, Ordering::AcqRel));
}

/// Generates a fresh `u64` to serve as a variable identifier.
pub fn next_u64() -> u64 {
    COUNTER.with(|c| {
        let mut counter = c.borrow_mut();
        let result = *counter;
        *counter += 128; // We assume there are fewer than 128 hardware threads.
        result
    })
}

/// Represents an index into the `Linked` linked-list data structure for explicit substitutions.
#[derive(Debug, Copy, Clone)]
pub struct DeBruijn(pub u32);

/// Represents an index into an `Entry` of the explicit substitution.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Index {
    Param(usize),
    Let(usize)
}

/// Represents an index to a variable or term in an explicit substitution.
#[derive(Debug, Copy, Clone)]
pub struct DeBruijnIndex(pub DeBruijn, pub Index);

/// An assignment to a metavariable with a `DeBruijnIndex` `head` and arguments `args`.
pub struct Assignment {
    pub head: DeBruijnIndex,
    pub args: Vec<S<Meta>>,

    /// `bind` (redundantly) contains the `Bind` of the `head` symbol in the context Gamma
    pub bind: W<Bind>,

    /// `changes` and `_owned_linked` allow us to return to the previous state during backtracking.
    pub changes: Vec<W<Meta>>,
    pub _owned_linked: Vec<S<Linked>>, // never accessed, only used for ownership.

    /// True if the codomain of `head` is not stuck on a metavariable, for heuristics.
    pub has_rigid_type: bool
}

/// The core data structure for terms and metavariables, consisting of an `assignment`
/// and additional information required for search, like the `Type` of the metavariable.
pub struct Meta {
    pub assignment: Option<Assignment>,
    /// The local variable context.
    pub gamma: ES,
    /// Equations that are stuck on this metavariable.
    pub equations: Vec<Equation>,
    /// The `Type` of this metavariable.
    pub typ: Option<Type>,
    /// The bindings introduced by this term.
    pub bindings: W<Indexed<S<Bind>>>,

    pub _owned_bindings: Option<S<Indexed<S<Bind>>>>, // exclusively for ownership purposes.

    /// Statistics and heuristics information.
    /// Statistics are generally accumulated in `stats_buffer`, but this must be reset during parallel processing,
    /// such that we can accumulate the updates from each thread. So, we transfer `stats_buffer` to `stats`.
    pub stats: SearchInfo,
    pub stats_buffer: SearchInfo,
    pub has_rigid_equation: bool,
    pub branching: f64,
    pub parent: Option<W<Meta>>
}

impl Meta {
    /// Creates an unassigned metavariable of a given `Type`.
    pub fn new(typ: Type) -> Self {
        Meta {
            assignment: None,
            gamma: typ.1.clone(),
            equations: Vec::new(),
            bindings: typ.0.borrow().codomain.borrow().bindings.clone(),
            _owned_bindings: None,
            stats: SearchInfo::new(),
            stats_buffer: SearchInfo::new(),
            has_rigid_equation: false,
            branching: 1.0,
            parent: None,
            typ: Some(typ)
        }
    }

    /// Checks that the assignment made to `self` does not violate an equation.
    /// If successful, outputs the new equations and updates the `changes` of the assignment.
    pub fn test_assignment(&mut self, var_type: &Type, prog_synth: bool) -> Option<Vec<Equation>> {
        let mut eqns = Vec::new();
        let assn = self.assignment.as_mut().unwrap();

        // check the type of `self` with the codomain of the `var_type`.
        if (Equation { premise: var_type.codomain(), goal: self.typ.as_ref().unwrap().codomain() }
            .reduce(&mut eqns, &mut assn.changes, &mut assn._owned_linked, prog_synth)) {
            // reduce existing equations
            if self.equations.iter().all(|eq|
                eq.reduce(&mut eqns, &mut assn.changes, &mut assn._owned_linked, prog_synth)
            ) {
                return Some(eqns)
            }
        }
        None
    }

    /// Perform an (already tested) assignment.
    pub fn assign(&mut self, mut assn: Assignment, eqns: Vec<Equation>) {
        // store equations with their stuck metavaraible
        for (item, slot) in eqns.into_iter().zip(assn.changes.iter_mut()) {
            slot.borrow_mut().equations.push(item)
        }
        self.assignment = Some(assn);
    }

    /// Unassign the metavariable, returning equations to their pre-assignment state.
    pub fn unassign(&mut self) {
        for meta in self.assignment.as_mut().unwrap().changes.iter_mut() {
            meta.borrow_mut().equations.pop();
        }
        self.assignment = None;
    }
}

/// A definitional (judgmental) equality between two `Term`s.
#[derive(Clone)]
pub struct Equation {
    /// `premise` is a subterm of the `codomain` of the `Type` of a variable
    pub premise: Term,
    /// `goal` is a subterm of the `codomain` of the `Type` of a metavariable
    pub goal: Term
}

impl Equation {
    /// Break down the equation into equations that are stuck on metavariables, added to `equations`.
    /// Returns false if the equation is violated.
    fn reduce(&self, equations: &mut Vec<Equation>, changes: &mut Vec<W<Meta>>,
              owned_linked: &mut Vec<S<Linked>>, prog_synth: bool) -> bool {
        if owned_linked.len() > 1000 { return false }
        // Reduce both sides of the equation.
        let WHNF(premise, premise_head, premise_meta) =
            self.premise.whnf(owned_linked, prog_synth);
        let WHNF(goal, goal_head, goal_meta) =
            self.goal.whnf(owned_linked, prog_synth);

        if premise_head.is_some() && (!prog_synth || premise_meta.is_none()) {
            if goal_head.is_some() && (!prog_synth || goal_meta.is_none()) {
                // If the head symbols are not equal, the equation is violated.
                if !premise_head.as_ref().unwrap().eq(goal_head.as_ref().unwrap()) { return false }

                // Identifier for the variables bound by the arguments of premise and goal.
                let var_id = next_u64();

                // Check that the arguments of premise and goal are equal.
                (0..premise.base.borrow().assignment.as_ref().unwrap().args.len()).all(|i|
                    Equation {
                        premise: premise.arg(i, Entry::vars(var_id), owned_linked),
                        goal: goal.arg(i, Entry::vars(var_id), owned_linked)
                    }.reduce(equations, changes, owned_linked, prog_synth)
                )
            } else {
                // goal is stuck, add an equation associated with goal_meta.
                equations.push(Equation { premise, goal });
                changes.push(goal_meta.unwrap());
                true
            }
        } else {
            // premise is stuck, add an equation associated with premise_meta.
            equations.push(Equation { premise, goal });
            changes.push(premise_meta.unwrap());
            true   
        }
    }
}


/// A substitution with a list of terms, all with the same explicit substitution.
/// Note that the explicit substitution does not contain the local variables unique to each
/// element of the vector.
pub struct Subst(pub WVec<S<Meta>>, pub ES);

impl Subst {
    /// Obtain `Term` `i` from the substitution, using `entry` for the local variables.
    pub fn get(&self, i: usize, entry: Entry, owned_linked: &mut Vec<S<Linked>>) -> Term {
        let base = self.0[i].downgrade();
        let bindings = base.borrow().bindings.clone();
        Term { es: self.1.append(Node { entry, bindings }, owned_linked), base }
    }
}

/// A list indexed by `Index`.
pub struct Indexed<T> {
    pub params: Vec<T>,
    pub lets: Vec<T>
}

impl<T> std::ops::Index<Index> for Indexed<T> {
    type Output = T;

    fn index(&self, index: Index) -> &Self::Output {
        match index {
            Param(i) => &self.params[i],
            Let(i) => &self.lets[i]
        }
    }
}

impl<T> Indexed<T> {
    /// We iterate over params first, as free variables are generally more important than consts.
    /// We iterate over params and lets in reverse order to prioritize dependently typed variables.
    pub fn iter(indexed: W<Indexed<T>>) -> Box<dyn Iterator<Item = Index>> {
        let params_iter = (0..indexed.borrow().params.len()).rev().map(Param);
        let lets_iter = (0..indexed.borrow().lets.len()).rev().map(Let);
        Box::new(params_iter.chain(lets_iter))
    }
}

pub struct SubstRange {
    pub range: Range<usize>,
    pub bindings: S<Indexed<S<Bind>>>
}

pub struct Symbol {
    pub bind: W<Bind>,
    pub children: Vec<usize>,
    pub entries: Vec<SubstRange>
}

pub struct Rule {
    pub pattern: Vec<Option<Symbol>>,
    pub replacement: S<Meta>
}

/// The `name` and `value` of a variable in the original input problem.
pub struct Bind {
    pub name: String,
    // Proof irrelevance, currently unused.
    pub irrelevant: bool,
    pub rules: Vec<Rule>,

    pub owned_bindings: Vec<S<Indexed<S<Bind>>>>
}

/// An explicit substitution entry, consisting of identifiers for the params and lets
/// and optionally a substitution or typing context. 
pub struct Entry {
    pub params_id: u64,
    pub lets_id: u64,
    pub subst: Option<Subst>,
    pub context: Option<Context>
}

impl Entry {
    /// Creates a substitution entry.
    pub fn subst(subst: Subst) -> Self {
        Self {
            params_id: next_u64(),
            lets_id: next_u64(),
            subst: Some(subst),
            context: None
        }
    }

    /// Creates a variable entry.
    pub fn vars(params_id: u64) -> Self {
        Self {
            params_id,
            lets_id: next_u64(),
            subst: None,
            context: None
        }
    }
}

/// An `entry` accompanied with the associated `bindings` from the original problem. 
pub struct Node {
    pub entry: Entry,
    pub bindings: W<Indexed<S<Bind>>>,
}

/// A linked list of `Node`
pub struct Linked {
    pub tail: Option<W<Linked>>,
    pub node: Node
}

/// Exclusively used for `get_head`. 
struct Head {
    var: Option<(Var, Option<W<Meta>>)>,
    term: Option<Term>,
    set_no_iota: bool
}

/// An Explicit Substitution, associating a `DeBruijnIndex` with a `Var` or `Term`.
#[derive(Clone)]
pub struct ES {
    pub linked: Option<W<Linked>>,
    pub iota_reduce: bool
}

impl ES {
    /// An empty explicit substitution.
    pub fn new() -> Self {
        ES { linked: None, iota_reduce: true }
    }

    /// Append a `Node` to the explicit substitution. 
    /// The caller is responsible for keeping `owned_linked` around as long as they wish to use the ES.
    pub fn append(&self, node: Node, owned_linked: &mut Vec<S<Linked>>) -> ES {
        // Zero-size optimization, when nothing needs to be added.
        if node.bindings.borrow().params.len() == 0 && node.bindings.borrow().lets.len() == 0 {
            return self.clone() // ES is just a pointer.
        }
        let link = S::new(Linked { tail: self.linked.to_owned(), node });
        let weak = link.downgrade();
        // Pass the ownership.
        owned_linked.push(link);
        ES { linked: Some(weak), iota_reduce: self.iota_reduce }
    }
    
    /// Returns the sublist rooted at node `db`.
    pub fn sub_es(&self, db: DeBruijn) -> ES {
        let mut curr = self.linked.as_ref().unwrap();
        for _ in 0..db.0 {
            curr = curr.borrow().tail.as_ref().expect("Index out of bounds!");
        }
        ES { linked: Some(curr.to_owned()), iota_reduce: self.iota_reduce }
    }
    
    /// Gets the variable at the root of this ES at the given `index`
    pub fn get_var(&self, index: Index) -> Var {
        let node = &self.linked.as_ref().unwrap().borrow().node;
        let entry_id = match index {
            Param(_) => node.entry.params_id,
            Let(_) => node.entry.lets_id
        };

        Var {
            bind: node.bindings.borrow()[index].downgrade(),
            index,
            entry_id
        }
    }

    /// Returns an iterator of `DeBruijnIndex` in this `ES``, along with the `Linked` they are rooted at.
    pub fn iter(&self) -> impl Iterator<Item = (DeBruijnIndex, W<Linked>)> {
        iter::successors(self.linked.clone(), |node| 
            node.borrow().tail.clone() // Iterate over the linked list.
        ).enumerate().flat_map(|(db, node)| 
            // Iterate over `Index` at this `DeBruijn`.
            Indexed::iter(node.borrow().node.bindings.clone()).map(move |item| 
                (DeBruijnIndex(DeBruijn(db as u32), item), node.clone())
            )
        )
    }

    /// Finds the `DeBruijnIndex` and `Bind` with a certain `name` in this `ES`.
    pub fn index_of(&self, name: &String) -> Option<(DeBruijnIndex, W<Bind>)> {
        self.iter().find(|(db, linked)| &linked.borrow().node.bindings.borrow()[db.1].borrow().name == name)
            .map(|(db, linked)| (db, linked.borrow().node.bindings.borrow()[db.1].downgrade()))
    }
}

/// A Term is a `DeBruijnIndex`-ed `base` with an explicit substitution `es` 
/// that associates a `DeBruijnIndex` with a variable or term.
#[derive(Clone)]
pub struct Term {
    pub base: W<Meta>,
    pub es: ES
}

/// A Term in weak head normal form, with the variable at the head, or the metavariable reduction is stuck on.
/// We allow both the variable and metavariable to be present for when we are stuck on the major argument of a recursor.
pub struct WHNF(pub Term, pub Option<Var>, pub Option<W<Meta>>);

pub struct Matcher<'a> {
    pub pattern: Iter<'a, Option<Symbol>>,
    pub replacement: Term
}

impl Term {
    /// Get the `i`th argument, applied with `entry`.
    fn arg(&self, i: usize, entry: Entry, owned_linked: &mut Vec<S<Linked>>) -> Term {
        let base = self.base.borrow().assignment.as_ref().unwrap().args[i].downgrade();
        Term { es: self.es.append(Node { entry, bindings: base.borrow().bindings.clone() }, owned_linked), base }
    }

    /// Computes the weak head normal form. 
    pub fn whnf(&self, owned_linked: &mut Vec<S<Linked>>, prog_synth: bool) -> WHNF {
        match &self.base.borrow().assignment {
            Some(assn) => {
                let es = self.es.sub_es(assn.head.0);

                // If there is a term at the head, recursively reduce it. Otherwise, the variable is the head symbol.
                if let Param(i) = assn.head.1 {
                    if let Some(subst) = &es.linked.as_ref().unwrap().borrow().node.entry.subst {
                        // If there is a substitution, and the index is a parameter, return the associated term in the substitution. 
                        let term = subst.get(i, Entry::subst(Subst(WVec::new(&assn.args), self.es.clone())), owned_linked);
                        return term.whnf(owned_linked, prog_synth);
                    }
                }

                let var = es.get_var(assn.head.1);
                if let Some(term) = self.reduce(&var.bind.borrow().rules, owned_linked, es) {
                    return term.whnf(owned_linked, prog_synth);
                } else {
                    return WHNF(self.clone(), Some(var), None);
                }
            },
            None => WHNF(self.clone(), None, Some(self.base.clone()))
        }
    }
}

impl <'a> Term {
    fn _reduce(&self, patterns: &mut Vec<Matcher<'a>>, owned_linked: &mut Vec<S<Linked>>) -> ControlFlow<Option<Term>> {
        if patterns.is_empty() { return ControlFlow::Continue(()); }
        let mut wildcards = Vec::new();
        
        let whnf = self.whnf(owned_linked, false);
        let mut ordering: Option<&Vec<usize>> = None;
        
        for i in (0..patterns.len()).rev() {
            let matcher = &mut patterns[i];
            if let Some(symbol) = matcher.pattern.next().unwrap() {
                if whnf.1.is_some() && symbol.bind.eq(&whnf.1.as_ref().unwrap().bind) {
                    ordering = Some(&symbol.children);
                    for entry in symbol.entries.iter() {
                        matcher.replacement.es = matcher.replacement.es.append(Node {
                            entry: Entry::subst(Subst(WVec::from(&whnf.0.base.borrow().assignment.as_ref().unwrap().args[entry.range.clone()]), whnf.0.es.clone())),
                            bindings: entry.bindings.downgrade()
                        }, owned_linked);
                    }
                    if matcher.pattern.len() == 0 {
                        return ControlFlow::Break(Some(matcher.replacement.clone()));
                    }
                } else {
                    patterns.remove(i);
                }
            }  else {
                wildcards.push(patterns.remove(i));
            }
        }

        if let Some(ordering) = ordering {
            for &i in ordering {
                let arg = whnf.0.arg(i, Entry::vars(next_u64()), owned_linked);
                arg._reduce(patterns, owned_linked)?;
            }
        }

        patterns.append(&mut wildcards); // TODO this changes the order
        ControlFlow::Continue(())
    }

    pub fn reduce(&self, patterns: &Vec<Rule>, owned_linked: &mut Vec<S<Linked>>, sub_es: ES) -> Option<Term> {
        let mut ordering = None;
        let mut matchers: Vec<Matcher> = Vec::new();
        for rule in patterns.iter() {
            // TODO super hacky.
            let mut iter = rule.pattern.iter();
            let symbol = iter.next().unwrap().as_ref().unwrap();
            ordering = Some(&symbol.children);
            let mut es = sub_es.clone();

            for entry in symbol.entries.iter() {
                es = es.append(Node {
                    entry: Entry::subst(Subst(WVec::from(&self.base.borrow().assignment.as_ref().unwrap().args[entry.range.clone()]), self.es.clone())),
                    bindings: entry.bindings.downgrade()
                }, owned_linked);
            }
            if iter.len() == 0 {
                return Some(Term { base: rule.replacement.downgrade(), es })
            }

            matchers.push(Matcher {
                pattern: iter,
                replacement: Term { base: rule.replacement.downgrade(), es }
            })
        }

        if let Some(ordering) = ordering {
            for &i in ordering {
                let arg = self.arg(i, Entry::vars(next_u64()), owned_linked);
                if let ControlFlow::Break(term) = arg._reduce(&mut matchers, owned_linked) {
                    return term;
                }
            }
        }

        return None
    }
}

/// A `DeBruijnIndex`-ed type, with a `codomain` (return type)
/// and parameter/let `types` 
pub struct TypeBase {
    pub codomain: S<Meta>,
    pub types: S<Indexed<Option<S<TypeBase>>>>
}

impl TypeBase {
    /// Create new metavariables to fill the parameters of this TypeBase.
    pub fn args_metas(&self, parent: W<Meta>) -> Vec<S<Meta>> {
        let arity = self.types.borrow().params.len();
        let mut args = Vec::with_capacity(arity);
        for i in 0..arity {
            args.push(S::new(Meta {
                assignment: None,
                typ: None,
                gamma: ES::new(),
                equations: Vec::new(),
                bindings: self.types.borrow()[Index::Param(i)].as_ref().unwrap().borrow().codomain.borrow().bindings.clone(),
                _owned_bindings: None,
                stats: SearchInfo::new(),
                stats_buffer: SearchInfo::new(),
                has_rigid_equation: false,
                branching: 1.0,
                parent: Some(parent.clone())
            }))
        }
        args
    }
}

/// A context with a list of types, all with the same explicit substitution.
/// Note that the explicit substitution does not contain the local variables unique to each element.
/// The `Bind`s correspond to the variables bound in this `Context`. 
pub struct Context(pub W<Indexed<Option<S<TypeBase>>>>, pub ES, pub W<Indexed<S<Bind>>>);

impl Context {
    /// Get the `i`th parameter type, specialized to `entry`.
    pub fn get(&self, i: Index, entry: Entry, owned_linked: &mut Vec<S<Linked>>) -> Type {
        let base = self.0.borrow()[i].as_ref().unwrap();
        Type(
            base.downgrade(), 
            self.1.append(Node {entry, bindings: base.borrow().codomain.borrow().bindings.clone() }, owned_linked),
            self.2.borrow()[i].downgrade()
        )
    }
}

/// A Type is a `DeBruijnIndex`-ed `TypeBase` with an explicit substitution `es` 
/// that associates a `DeBruijnIndex` with a variable or term.
/// The `Bind` corresponds to the variable in the original problem that has this `Type`. 
#[derive(Clone)]
pub struct Type(pub W<TypeBase>, pub ES, pub W<Bind>);

impl Type {
    /// Get the return type, as a `Term`.
    pub fn codomain(&self) -> Term {
        Term { base: self.0.borrow().codomain.downgrade(), es: self.1.clone() }
    }

    /// Get the parameter types.
    pub fn params(&self) -> Context {
        let bindings = self.0.borrow().codomain.borrow().bindings.clone();
        Context(self.0.borrow().types.downgrade(), self.1.clone(), bindings)
    }
}

/// A variable from entry `entry_id` at position `index`,
/// associated with `bind` from the original problem. 
pub struct Var {
    entry_id: u64,
    index: Index,
    pub bind: W<Bind>
}

impl Var {
    /// Two variables from the same entry at the same position are equal.
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index && self.entry_id == other.entry_id
    }
}