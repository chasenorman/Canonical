use Index::*;
use crate::memory::{S, W, WVec};
use std::sync::atomic::{AtomicU64, Ordering};
use std::iter;
use crate::stats::SearchInfo;
use mimalloc::MiMalloc;
use std::cell::RefCell;
use std::ops::ControlFlow;
use core::slice::Iter;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

/// Used to give each hardware thread a unique ID.
static THREAD_COUNTER: AtomicU64 = AtomicU64::new(0);

thread_local! {
    /// Each thread generates a disjoint set of `u64`s, starting from the hardware thread ID.
    static COUNTER: RefCell<u64> = RefCell::new(THREAD_COUNTER.fetch_add(1, Ordering::AcqRel));
}

pub fn guard_overflow() {
    if stacker::remaining_stack().unwrap() < 32 * 1024 { panic!("Stack overflow.") }
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
    pub bind: W<Decl>,

    /// `changes` and `_owned_linked` allow us to return to the previous state during backtracking.
    pub changes: Vec<W<Meta>>,
    pub _owned_linked: Vec<S<Linked>>, // never accessed, only used for ownership.

    /// True if the codomain of `head` is not stuck on a metavariable, for heuristics.
    pub has_rigid_type: bool,
    pub var_type: Option<Type>
}

/// The core data structure for terms and metavariables, consisting of an `assignment`
/// and additional information required for search, like the `Type` of the metavariable.
pub struct Meta {
    pub assignment: Option<Assignment>,
    /// The local variable context.
    pub gamma: ES,
    /// Constraints that are stuck on this metavariable.
    pub constraints: Vec<Box<dyn Constraint>>,

    /// The `Type` of this metavariable.
    pub typ: Option<Type>,
    /// The bindings introduced by this term.
    pub bindings: W<Indexed>,
    pub from_original_problem: bool,

    pub _owned_bindings: Option<S<Indexed>>, // exclusively for ownership purposes.

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
            constraints: Vec::new(),
            bindings: typ.0.borrow().typ.as_ref().unwrap().borrow().bindings.clone(),
            from_original_problem: false,
            _owned_bindings: None,
            stats: SearchInfo::new(),
            stats_buffer: SearchInfo::new(),
            has_rigid_equation: false,
            branching: 1.0,
            parent: None,
            typ: Some(typ)
        }
    }

    /// Checks that the assignment made to `self` does not violate a constraint.
    /// If successful, outputs the new constraints and updates the `changes` of the assignment.
    pub fn test_assignment(&mut self, this: W<Meta>) -> Option<Vec<Box<dyn Constraint>>> {
        let mut new_constraints: Vec<Box<dyn Constraint>> = Vec::new();
        let assn = self.assignment.as_mut().unwrap();

        // check the type of `self` with the codomain of the `var_type
        if (!Equation { premise: assn.var_type.as_ref().unwrap().codomain(), goal: self.typ.as_ref().unwrap().codomain(), allow_redexes: false }
            .reduce(&mut new_constraints, &mut assn.changes, &mut assn._owned_linked)) { return None; }

        if !assn.bind.borrow().redexes.iter().all(|redex|
            RedexConstraint {
                instructions: WVec::new(redex),
                position: 0,
                blame: this.clone(),
            }.reduce(&mut new_constraints, &mut assn.changes, &mut assn._owned_linked)
        ) { return None; }

        if !self.constraints.iter().all(|c|
            c.reduce(&mut new_constraints, &mut assn.changes, &mut assn._owned_linked)
        ) { return None }

        return Some(new_constraints);
    }

    /// Perform an (already tested) assignment.
    pub fn assign(&mut self, mut assn: Assignment, constraints: Vec<Box<dyn Constraint>>) {
        // store constraints with their stuck metavariable
        for (item, slot) in constraints.into_iter().zip(assn.changes.iter_mut()) {
            slot.borrow_mut().constraints.push(item)
        }
        self.assignment = Some(assn);
    }

    /// Unassign the metavariable, returning constraints to their pre-assignment state.
    pub fn unassign(&mut self) {
        let assn = self.assignment.as_mut().unwrap();
        for meta in assn.changes.iter_mut() {
            meta.borrow_mut().constraints.pop();
        }
        self.assignment = None;
    }
}

pub trait Constraint: std::any::Any {
    /// Propagate the constraint on the basis of new assignments.
    fn reduce(&self, constraints: &mut Vec<Box<dyn Constraint>>, changes: &mut Vec<W<Meta>>,
              owned_linked: &mut Vec<S<Linked>>) -> bool;

    /// Whether this constraint enforces an assignment on the stuck metavariable.
    fn rigid(&self) -> bool { false }
}

/// A definitional (judgmental) equality between two `Term`s.
#[derive(Clone)]
pub struct Equation {
    /// `premise` is a subterm of the `codomain` of the `Type` of a variable
    pub premise: Term,
    /// `goal` is a subterm of the `codomain` of the `Type` of a metavariable
    pub goal: Term,
    pub allow_redexes: bool
}

#[derive(Clone)]
pub struct RedexConstraint {
    pub instructions: WVec<Instruction>,
    pub position: usize,
    /// The metavariable this constraint is currently walking from.
    pub blame: W<Meta>
}

impl Constraint for RedexConstraint {
    fn reduce(&self, constraints: &mut Vec<Box<dyn Constraint>>, changes: &mut Vec<W<Meta>>,
              _owned_linked: &mut Vec<S<Linked>>) -> bool {
        let mut blame = self.blame.clone();
        let mut i = self.position;
        loop {
            let Some(assn) = &blame.borrow().assignment else {
                constraints.push(Box::new(RedexConstraint {
                    instructions: self.instructions.clone(),
                    position: i,
                    blame: blame.clone(),
                }));
                changes.push(blame);
                return true
            };

            if !assn.bind.eq(&self.instructions[i].bind) {
                return true;
            }
            if i == self.instructions.len() - 1 {
                return false;
            }
            for _ in 0..self.instructions[i].parents {
                blame = blame.borrow().parent.as_ref().unwrap().clone();
            }
            blame = blame.borrow().assignment.as_ref().unwrap().args[self.instructions[i].child].downgrade();
            i += 1;
        }
    }
}


impl Constraint for Equation {
    /// Break down the equation into equations that are stuck on metavariables, added to `constraints`.
    /// Returns false if the equation is violated.
    fn reduce(&self, constraints: &mut Vec<Box<dyn Constraint>>, changes: &mut Vec<W<Meta>>,
              owned_linked: &mut Vec<S<Linked>>) -> bool {
        if owned_linked.len() > 1000 { return false }
        // Reduce both sides of the equation.
        match self.premise.whnf::<true, ()>(owned_linked, &mut (), self.allow_redexes) {
            WHNF(premise, Head::Var(lhs)) => {
                match self.goal.whnf::<true, ()>(owned_linked, &mut (), self.allow_redexes) {
                    WHNF(goal, Head::Var(rhs)) => {
                        // If the head symbols are not equal, the equation is violated.
                        if !lhs.eq(&rhs) { return false }

                        // Identifier for the variables bound by the arguments of premise and goal.
                        let var_id = next_u64();

                        // Check that the arguments of premise and goal are equal.
                        (0..premise.base.borrow().assignment.as_ref().unwrap().args.len()).all(|i|
                            Equation {
                                premise: premise.arg(i, Entry::vars(var_id), owned_linked),
                                goal: goal.arg(i, Entry::vars(var_id), owned_linked),
                                allow_redexes: self.allow_redexes
                            }.reduce(constraints, changes, owned_linked)
                        )
                    }
                    WHNF(goal, Head::Meta(rhs)) => {
                        // goal is stuck, add an equation associated with goal_meta.
                        constraints.push(Box::new(Equation { premise, goal, allow_redexes: self.allow_redexes }));
                        changes.push(rhs);
                        true
                    }
                }
            }
            WHNF(premise, Head::Meta(lhs)) => {
                // premise is stuck, add an equation associated with premise_meta.
                constraints.push(Box::new(Equation { premise, goal: self.goal.clone(), allow_redexes: self.allow_redexes }));
                changes.push(lhs);
                true
            }
        }
    }

    fn rigid(&self) -> bool {
        matches!(self.premise.whnf::<true, ()>(&mut Vec::new(), &mut (), self.allow_redexes).1, Head::Var(_)) ||
        matches!(self.goal.whnf::<true, ()>(&mut Vec::new(), &mut (), self.allow_redexes).1, Head::Var(_))
    }
}


/// A substitution with a list of terms, all with the same explicit substitution.
/// Note that the explicit substitution does not contain the local variables unique to each
/// element of the vector.
#[derive(Clone)]
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
pub struct Indexed {
    pub params: Vec<S<Decl>>,
    pub lets: Vec<S<Decl>>
}

impl std::ops::Index<Index> for Indexed {
    type Output = S<Decl>;

    fn index(&self, index: Index) -> &Self::Output {
        match index {
            Param(i) => &self.params[i],
            Let(i) => &self.lets[i]
        }
    }
}

impl Indexed {
    /// We iterate over params first, as free variables are generally more important than consts.
    /// We iterate over params and lets in reverse order to prioritize dependently typed variables.
    pub fn iter(indexed: &Indexed) -> impl Iterator<Item = Index> + '_ {
        let params_iter = (0..indexed.params.len()).rev().map(Param);
        let lets_iter = (0..indexed.lets.len()).rev().map(Let);
        params_iter.chain(lets_iter)
    }
}

pub struct Instruction {
    pub bind: W<Decl>,
    pub parents: u32,
    pub child: usize
}

pub struct Symbol {
    pub bind: W<Decl>,
    pub children: Vec<usize>,
    pub bindings: S<Indexed>
}

pub struct Rule {
    pub pattern: Vec<Option<Symbol>>,
    pub replacement: S<Meta>,
    pub attribution: Vec<String>
}

/// The `name` and `value` of a variable in the original input problem.
// pub struct Bind {
//     pub name: String,
//     pub constraints: Vec<(S<Meta>, S<Meta>)>,
//     pub rules: Vec<Rule>,
//     pub redexes: Vec<Vec<Instruction>>,

//     pub owned_bindings: Vec<S<Indexed<S<Bind>>>>
// }

pub struct Decl {
    pub name: String,
    pub constraints: Vec<(S<Meta>, S<Meta>, bool)>,
    pub rules: Vec<Rule>,
    pub redexes: Vec<Vec<Instruction>>,
    pub typ: Option<S<Meta>>,
    pub _owned_bindings: Vec<S<Indexed>>
}

impl Decl {
    pub fn new(name: String) -> Self {
        Decl {
            name,
            constraints: Vec::new(),
            rules: Vec::new(),
            redexes: Vec::new(),
            typ: None,
            _owned_bindings: Vec::new()
        }
    }
}

/// An explicit substitution entry, consisting of identifiers for the params and lets
/// and optionally a substitution or typing context. 
#[derive(Clone)]
pub struct Entry {
    pub params_id: u64,
    pub lets_id: u64,
    pub subst: Option<Subst>,
    pub context: Option<Type>
}

impl Entry {
    /// Creates a substitution entry.
    pub fn subst(subst: Subst, lets_id: u64) -> Self {
        Self {
            params_id: next_u64(),
            lets_id,
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
    pub bindings: W<Indexed>,
}

/// A linked list of `Node`
pub struct Linked {
    pub tail: Option<W<Linked>>,
    pub node: Node
}

/// An Explicit Substitution, associating a `DeBruijnIndex` with a `Var` or `Term`.
#[derive(Clone)]
pub struct ES {
    pub linked: Option<W<Linked>>
}

impl ES {
    /// An empty explicit substitution.
    pub fn new() -> Self {
        ES { linked: None }
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
        ES { linked: Some(weak) }
    }
    
    /// Returns the sublist rooted at node `db`.
    pub fn sub_es(&self, db: DeBruijn) -> ES {
        let mut curr = self.linked.as_ref().unwrap();
        for _ in 0..db.0 {
            curr = curr.borrow().tail.as_ref().expect("Index out of bounds!");
        }
        ES { linked: Some(curr.to_owned()) }
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
        ).enumerate().flat_map(move |(db, node)| {
            let indices: Vec<Index> = Indexed::iter(node.borrow().node.bindings.borrow()).collect();
            indices.into_iter().map(move |item| (DeBruijnIndex(DeBruijn(db as u32), item), node.clone()))
        })
    }

    /// Finds the `DeBruijnIndex` and `Bind` with a certain `name` in this `ES`.
    pub fn index_of(&self, name: &String) -> Option<(DeBruijnIndex, W<Decl>)> {
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

pub enum Head {
    Var(Var),
    Meta(W<Meta>)
}

/// A Term in weak head normal form, with the variable at the head, or the metavariable reduction is stuck on.
/// We allow both the variable and metavariable to be present for when we are stuck on the major argument of a recursor.
pub struct WHNF(pub Term, pub Head);

pub struct Matcher<'a> {
    pub pattern: Iter<'a, Option<Symbol>>,
    pub replacement: Term,
    pub rule: &'a Rule
}

pub trait Attribution {
    fn attribute(&mut self, s: &Rule);
}

impl Attribution for () {
    fn attribute(&mut self, _: &Rule) {}
}

impl Attribution for Vec<String> {
    fn attribute(&mut self, s: &Rule) {
        self.append(&mut s.attribution.clone());
    }
}

impl Term {
    /// Get the `i`th argument, applied with `entry`.
    pub fn arg(&self, i: usize, entry: Entry, owned_linked: &mut Vec<S<Linked>>) -> Term {
        let base = self.base.borrow().assignment.as_ref().unwrap().args[i].downgrade();
        Term { es: self.es.append(Node { entry, bindings: base.borrow().bindings.clone() }, owned_linked), base }
    }

    /// Computes the weak head normal form.
    pub fn whnf<const RULES: bool, C: Attribution>(&self, owned_linked: &mut Vec<S<Linked>>, attribution: &mut C, allow_redexes: bool) -> WHNF {
        guard_overflow();
        if let Some(assn) = &self.base.borrow().assignment {
            let es = self.es.sub_es(assn.head.0);

            // If there is a term at the head, recursively reduce it. Otherwise, the variable is the head symbol.
            if let Param(i) = assn.head.1 {
                if let Some(subst) = &es.linked.as_ref().unwrap().borrow().node.entry.subst {
                    let lets_id = subst.0[i].borrow().gamma.linked.as_ref().map_or_else(next_u64, |linked| linked.borrow().node.entry.lets_id);
                    let term = subst.get(i, Entry::subst(Subst(WVec::new(&assn.args), self.es.clone()), lets_id), owned_linked);
                    return term.whnf::<RULES, C>(owned_linked, attribution, allow_redexes);
                }
            }

            let var = es.get_var(assn.head.1);
            let bind = var.bind.clone();
            let whnf = WHNF(self.clone(), Head::Var(var));
            if RULES && !bind.borrow().rules.is_empty() {
                let mut matchers = bind.borrow().rules.iter().map(|rule| Matcher {
                    pattern: rule.pattern.iter(),
                    replacement: Term { base: rule.replacement.downgrade(), es: es.clone() },
                    rule: &rule
                }).collect();
                let mut stuck : Option<W<Meta>> = None;
                let matched = whnf.pattern_match(&mut matchers, owned_linked, attribution, allow_redexes || whnf.0.base.borrow().from_original_problem, &mut stuck);
                if let ControlFlow::Break((term, rule)) = matched {
                    attribution.attribute(rule);
                    return term.whnf::<RULES, C>(owned_linked, attribution, allow_redexes);
                }
                if let Some(meta) = stuck {
                    return WHNF(self.clone(), Head::Meta(meta));
                }
            }
            whnf
        } else {
            WHNF(self.clone(), Head::Meta(self.base.clone()))
        }
    }
}

impl <'a> WHNF {
    fn pattern_match<C: Attribution>(&self, patterns: &mut Vec<Matcher<'a>>, owned_linked: &mut Vec<S<Linked>>, attribution: &mut C, can_stuck: bool, stuck: &mut Option<W<Meta>>) -> ControlFlow<(Term, &'a Rule)> {
        guard_overflow();
        match &self.1 {
            Head::Meta(meta) => {
                patterns.retain_mut(|matcher| 
                    matcher.pattern.next().unwrap().is_none()
                );
                if can_stuck {
                    stuck.replace(meta.clone());
                }
                ControlFlow::Continue(())
            }
            Head::Var(var) => {
                let mut recursive = Vec::new();
                let mut ordering: Option<&Vec<usize>> = None;
                
                for i in (0..patterns.len()).rev() {
                    if let Some(symbol) = patterns[i].pattern.next().unwrap() {
                        let mut matcher = patterns.remove(i);
                        if symbol.bind.eq(&var.bind) {
                            ordering = Some(&symbol.children);
                            matcher.replacement.es = matcher.replacement.es.append(Node {
                                entry: Entry::subst(Subst(WVec::new(&self.0.base.borrow().assignment.as_ref().unwrap().args), self.0.es.clone()), next_u64()),
                                bindings: symbol.bindings.downgrade()
                            }, owned_linked);
                            if matcher.pattern.len() == 0 {
                                return ControlFlow::Break((matcher.replacement.clone(), matcher.rule));
                            }
                            recursive.push(matcher);
                        }
                    }
                }

                if let Some(ordering) = ordering {
                    for &i in ordering {
                        let arg = self.0.arg(i, Entry::vars(next_u64()), owned_linked);
                        arg.whnf::<true, C>(owned_linked, attribution, can_stuck).pattern_match(&mut recursive, owned_linked, attribution, can_stuck, stuck)?;
                        if recursive.is_empty() { break; }
                    }
                }

                patterns.append(&mut recursive); // TODO this changes the order
                ControlFlow::Continue(())
            }
        }
    }
}

pub enum Polarity { 
    Premise, Goal
}

/// A `DeBruijnIndex`-ed type, with a `codomain` (return type)
/// and parameter/let `types` 
// pub struct TypeBase {
//     pub codomain: S<Meta>,
//     pub types: S<Indexed<Option<S<TypeBase>>>>,
//     pub bind: W<Bind>
// }

impl Meta {
    /// Create new metavariables to fill the parameters of this TypeBase.
    pub fn args_metas(&self, parent: Option<W<Meta>>) -> Vec<S<Meta>> {
        let arity = self.bindings.borrow().params.len();
        let mut args = Vec::with_capacity(arity);
        for i in 0..arity {
            args.push(S::new(Meta {
                assignment: None,
                typ: None,
                gamma: ES::new(),
                constraints: Vec::new(),
                bindings: self.bindings.borrow()[Index::Param(i)].borrow().typ.as_ref().unwrap().borrow().bindings.clone(),
                from_original_problem: false,
                _owned_bindings: None,
                stats: SearchInfo::new(),
                stats_buffer: SearchInfo::new(),
                has_rigid_equation: false,
                branching: 1.0,
                parent: parent.clone()
            }))
        }
        args
    }
}

/// A Type is a `DeBruijnIndex`-ed `TypeBase` with an explicit substitution `es` 
/// that associates a `DeBruijnIndex` with a variable or term.
/// The `Bind` corresponds to the variable in the original problem that has this `Type`. 
#[derive(Clone)]
pub struct Type(pub W<Decl>, pub ES);

impl Type {
    /// Get the return type, as a `Term`.
    pub fn codomain(&self) -> Term {
        Term { base: self.0.borrow().typ.as_ref().unwrap().downgrade(), es: self.1.clone() }
    }

    /// Get the `i`th parameter type, specialized to `entry`.
    pub fn get(&self, i: Index, entry: Entry, owned_linked: &mut Vec<S<Linked>>) -> Type {
        let base = &self.0.borrow().typ.as_ref().unwrap().borrow().bindings.borrow()[i];
        Type(
            base.downgrade(), 
            self.1.append(Node {entry, bindings: base.borrow().typ.as_ref().unwrap().borrow().bindings.clone() }, owned_linked),
        )
    }
}

/// A variable from entry `entry_id` at position `index`,
/// associated with `bind` from the original problem. 
pub struct Var {
    entry_id: u64,
    index: Index,
    pub bind: W<Decl>
}

impl Var {
    /// Two variables from the same entry at the same position are equal.
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index && self.entry_id == other.entry_id
    }
}
