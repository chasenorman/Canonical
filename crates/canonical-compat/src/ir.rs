use canonical_core::core::*;
use canonical_core::memory::{S, W};
use canonical_core::search::test;
use canonical_core::compiler::compile;
use std::fmt;
use serde::{Serialize, Deserialize};
use std::fs::File;
use crate::reduction::*;
use canonical_core::stats::SearchInfo;
use std::any::Any;

/// Render a constraint stuck on a metavariable for the debug tooltip, recovering its concrete type.
fn constraint_html(c: &dyn Constraint, owned_linked: &mut Vec<S<Linked>>) -> String {
    if let Some(eqn) = (c as &dyn Any).downcast_ref::<Equation>() {
        let lhs = IRSpine::from_body::<true>(eqn.premise.whnf::<true, ()>(owned_linked, &mut (), eqn.allow_redexes), false);
        let rhs = IRSpine::from_body::<true>(eqn.goal.whnf::<true, ()>(owned_linked, &mut (), eqn.allow_redexes), false);
        format!("<div class='constraint'>{lhs} ≡ {rhs}</div>")
    } else if let Some(redex) = (c as &dyn Any).downcast_ref::<RedexConstraint>() {
        let path = (redex.position..redex.instructions.len())
            .map(|i| redex.instructions[i].bind.borrow().name.clone())
            .collect::<Vec<_>>()
            .join(" → ");
        format!("<div class='constraint'>redex: {path}</div>")
    } else {
        String::new()
    }
}

#[derive(PartialEq, Eq, Serialize, Deserialize)]
pub struct IREquation {
    pub lhs: IRSpine,
    pub rhs: IRSpine,
    #[serde(skip)]
    pub attribution: Vec<String>,
    pub is_redex: bool
}

/// A declaration, with a variable `name`, optional `typ`, and defining `equations`.
#[derive(PartialEq, Eq, Serialize, Deserialize)]
pub struct IRDecl {
    pub name: String,
    pub typ: Option<IRExpr>,
    pub equations: Vec<IREquation>
}

#[derive(PartialEq, Eq, Serialize, Deserialize)]
pub struct IRSpine {
    pub head: String,
    pub args: Vec<IRExpr>,
    #[serde(skip)]
    pub premise_rules: Vec<String>
}

/// An expression is an n-ary, β-normal, η-long λ expression:
/// `λ params lets . head args`.
/// Read as a type, it is an n-ary Π-type with codomain `spine`,
/// where the declarations carry the domain types.
#[derive(PartialEq, Eq, Serialize, Deserialize)]
pub struct IRExpr {
    pub params: Vec<IRDecl>,
    pub lets: Vec<IRDecl>,
    pub spine: IRSpine,
    #[serde(skip)]
    pub goal_rules: Vec<String>
}

impl IRDecl {
    pub fn to_bind(&self) -> Decl { Decl::new(self.name.clone()) }

    /// Translate this declaration, compiling `equations` and `typ` into `decl`.
    /// Equations on a let (`LET`) define reduction, as rewrite rules and redexes;
    /// equations on a param constrain the instantiation of its variables, checked as `Equation`s.
    fn translate<const LET: bool>(&self, decl: &mut S<Decl>, es: &ES, owned_linked: &mut Vec<S<Linked>>) {
        if LET {
            let mut owned_bindings = Vec::new();
            decl.borrow_mut().rules = to_rules(&self.equations, es, owned_linked, &mut owned_bindings);
            decl.borrow_mut().redexes = to_redexes(&self.equations, es);
            decl.borrow_mut()._owned_bindings = owned_bindings;
        } else {
            decl.borrow_mut().constraints = self.equations.iter().map(|c| (
                S::new(c.lhs.to_body(es.clone(), S::new(Indexed { params: Vec::new(), lets: Vec::new() }), Vec::new())),
                S::new(c.rhs.to_body(es.clone(), S::new(Indexed { params: Vec::new(), lets: Vec::new() }), Vec::new())),
                c.is_redex
            )).collect();
        }
        decl.borrow_mut().typ = self.typ.as_ref().map(|t| t.to_expr(es));
    }

    /// Translate this declaration into a `Decl` to be solved for by a `Prover`.
    /// The type and equations are typed under an ES with a dummy entry binding `self.name`,
    /// which `Prover::new` recreates as a substitution containing the metavariable itself.
    pub fn to_problem(&self, owned_linked: &mut Vec<S<Linked>>) -> S<Decl> {
        assert!(self.typ.is_some(), "Declaration {} has no type.", self.name);
        let mut decl = S::new(self.to_bind());

        // The dummy entry with the name of the problem.
        let bindings = S::new(Indexed { params: vec![S::new(self.to_bind())], lets: Vec::new() });
        let es = ES::new().append(Node { entry: Entry::vars(next_u64()), bindings: bindings.downgrade() }, owned_linked);
        decl.borrow_mut()._owned_bindings.push(bindings);

        // Translate the type under the dummy entry, and wait to translate the equations
        // until the second node with the variables of the type is created.
        decl.borrow_mut().typ = Some(self.typ.as_ref().unwrap().to_expr(&es));
        let gamma = decl.borrow().typ.as_ref().unwrap().borrow().gamma.clone();
        decl.borrow_mut().constraints = self.equations.iter().map(|c| (
            S::new(c.lhs.to_body(gamma.clone(), S::new(Indexed { params: Vec::new(), lets: Vec::new() }), Vec::new())),
            S::new(c.rhs.to_body(gamma.clone(), S::new(Indexed { params: Vec::new(), lets: Vec::new() }), Vec::new())),
            c.is_redex
        )).collect();

        compile(Type(decl.downgrade(), es));
        decl
    }
}

fn get_rules(term: &Term) -> Vec<String> {
    let mut attribution = Vec::new();
    let mut owned_linked = Vec::new();
    _get_rules(term, &mut attribution, &mut owned_linked);
    attribution
}

fn _get_rules(term: &Term, attribution: &mut Vec<String>, owned_linked: &mut Vec<S<Linked>>) {
    let whnf = term.whnf::<true, Vec<String>>(owned_linked, attribution, false);
    if whnf.0.base.borrow().assignment.is_some() {
        let len = whnf.0.base.borrow().assignment.as_ref().unwrap().args.len();
        for i in 0..len {
            let arg = whnf.0.arg(i, Entry::vars(next_u64()), owned_linked);
            _get_rules(&arg, attribution, owned_linked);
        }
    }
}

/// Create a `Decl` with the `preferred_name`, appending a suffix such that it is not contained in `es`.
fn disambiguate_bind(preferred_name: &String, es: &ES) -> Decl {
    let mut count = 0;
    let mut name = preferred_name.clone();
    while es.index_of( &name).is_some() {
        count += 1;
        name = preferred_name.clone() + &count.to_string();
    }
    Decl::new(name)
}

/// Construct a copy of `bindings` such that the names are not already in `es`.
fn disambiguate(bindings: W<Indexed>, es: &ES) -> Indexed {
    let params = bindings.borrow().params.iter().map(
        |b| S::new(disambiguate_bind(&b.borrow().name, es))).collect();
    let lets = bindings.borrow().lets.iter().map(
        |b| S::new(disambiguate_bind(&b.borrow().name, es))).collect();
    Indexed { params, lets }
}

impl IRSpine {
    pub fn from_body<const RULES: bool>(WHNF(whnf, head): WHNF, html: bool) -> IRSpine {
        let mut owned_linked = Vec::new();
            
        match &head {
            Head::Meta(meta) => {
                if html {
                    IRSpine { head: Self::meta_html(meta.clone()), args: Vec::new(), premise_rules: Vec::new() }
                } else {
                    Self::from_meta::<RULES>(whnf, meta.clone())
                }
            }
            Head::Var(var) => {
                let mut _owned_bindings = Vec::new();

                let args = whnf.base.borrow().assignment.as_ref().unwrap().args.iter().map(|arg| {
                    let bindings = S::new(disambiguate(arg.borrow().bindings.clone(), &whnf.es));
                    let wbindings = bindings.downgrade();
                    let es = whnf.es.append(Node {
                        entry: Entry::vars(next_u64()),
                        bindings: wbindings.clone()
                    }, &mut owned_linked);
                    _owned_bindings.push(bindings);
                    IRExpr::from_lambda::<RULES>(Term { base: arg.downgrade(), es }, wbindings.clone(), html)
                }).collect();

                IRSpine {
                    head: var.bind.borrow().name.clone(),
                    args,
                    premise_rules: whnf.base.borrow().assignment.as_ref().unwrap().var_type.as_ref().map(|typ| get_rules(&typ.codomain())).unwrap_or_default()
                }
            }
        }
    }

    fn from_meta<const RULES: bool>(term: Term, stuck: W<Meta>) -> IRSpine {
        let mut args = Vec::new();
        if !stuck.borrow().bindings.borrow().params.is_empty() {
            if let Some(subst) = &term.es.linked.as_ref().unwrap().borrow().node.entry.subst {
                let mut _owned_bindings = Vec::new();
                for i in 0..subst.0.len() {
                    let mut owned_linked = Vec::new();
                    let arg = subst.0[i].downgrade();
                    let bindings = S::new(disambiguate(arg.borrow().bindings.clone(), &subst.1));
                    let wbindings = bindings.downgrade();
                    let es = subst.1.append(Node {
                        entry: Entry::vars(next_u64()),
                        bindings: wbindings.clone()
                    }, &mut owned_linked);
                    _owned_bindings.push(bindings);
                    args.push(IRExpr::from_lambda::<RULES>(Term { base: arg, es }, wbindings.clone(), false))
                }
            }
        }
        IRSpine {
            head: "?&NoBreak;".to_string() + &stuck.borrow().typ.as_ref().unwrap().0.borrow().name,
            args,
            premise_rules: Vec::new()
        }
    }

    fn meta_html(meta: W<Meta>) -> String {
        let varname = "?&NoBreak;".to_string() + &meta.borrow().typ.as_ref().unwrap().0.borrow().name;
        let meta_id = meta.borrow() as *const Meta as usize;

        let options = meta.borrow().gamma.iter_unify(
            meta.borrow().typ.as_ref().unwrap().0.clone()
        ).filter_map(|(db, linked)| {
            if let Some(Some(result)) = test(db, linked, meta.clone()) {
                let name = result.0.bind.borrow().name.clone();

                let (index, def) = match db.1 {
                    Index::Param(i) => (i, false),
                    Index::Let(i) => (i, true)
                };
                let debruijn = db.0.0;
                
                return Some(format!("<button class='option' onclick='assign({meta_id}, {debruijn}, {index}, {def})'>{name}</button>"));
            }
            None
        }).reduce(|a, b| format!("{a}</br>{b}")).unwrap_or("<div class='fail'>No Options</div>".to_string());
        let mut owned_linked = Vec::new();
        let typ = IRSpine::from_body::<true>(meta.borrow().typ.as_ref().unwrap().codomain().whnf::<true, ()>(&mut owned_linked, &mut (), false), false);

        let inner = meta.borrow().constraints.iter()
            .map(|c| constraint_html(c.as_ref(), &mut owned_linked))
            .fold("".to_string(), |a, b| a + &b);
        let constraints = if inner.is_empty() {
            "".to_string()
        } else {
            format!("<div class='constraints'>{inner}</div>")
        };

        let tooltiptext = format!("<div class='tooltiptext'><div class='provers'>{options}</div>{constraints}<div class='type'>{typ}</div></div>");
        let tooltip = format!("<div class='tooltip'><span class='meta'>{varname}</span>{tooltiptext}</div>");
        return format!("<label><input type='radio' name='meta' id='{meta_id}' value='{meta_id}'>{tooltip}</label>")
    }

    /// Finds the head `DeBruijnIndex` in the `es` and creates a Meta with `bindings` and recursively converted arguments.
    pub fn to_body(&self, es: ES, bindings: S<Indexed>, owned_linked: Vec<S<Linked>>) -> Meta {
        let (head, bind) = es.index_of(&self.head).expect(&format!("Undeclared variable: {}", self.head));
        let args = self.args.iter().map(|t| t.to_expr(&es)).collect();
 
        Meta {
            assignment: Some(Assignment { head, args, bind, changes: Vec::new(), _owned_linked: owned_linked, has_rigid_type: true, var_type: None }),
            typ: None,
            gamma: es,
            constraints: Vec::new(),
            bindings: bindings.downgrade(),
            from_original_problem: true,
            _owned_bindings: Some(bindings),
            stats: SearchInfo::new(),
            stats_buffer: SearchInfo::new(),
            has_rigid_equation: false,
            branching: 1.0,
            parent: None,
        }
    }
}

impl IRExpr {
    /// Extend `es` with fresh `Decl`s for `self.params` and `self.lets`, without compiling equations.
    pub fn add_local(&self, es: &ES, owned_linked: &mut Vec<S<Linked>>) -> (ES, S<Indexed>) {
        let bindings = S::new(Indexed {
            params: self.params.iter().map(|d| S::new(d.to_bind())).collect(),
            lets: self.lets.iter().map(|d| S::new(d.to_bind())).collect()
        });

        let node = Node {
            entry: Entry { params_id: next_u64(), lets_id: next_u64(), subst: None, context: None },
            bindings: bindings.downgrade()
        };
        (es.append(node, owned_linked), bindings)
    }

    /// Convert to the codomain `Meta`, translating each declaration in the extended ES.
    pub fn to_expr(&self, es: &ES) -> S<Meta> {
        let mut owned_linked = Vec::new();
        let (es, mut bindings) = self.add_local(es, &mut owned_linked);

        for (decl, d) in bindings.borrow_mut().params.iter_mut().zip(self.params.iter()) {
            d.translate::<false>(decl, &es, &mut owned_linked);
        }
        for (decl, d) in bindings.borrow_mut().lets.iter_mut().zip(self.lets.iter()) {
            d.translate::<true>(decl, &es, &mut owned_linked);
        }

        S::new(self.spine.to_body(es, bindings, owned_linked))
    }

    pub fn from_lambda<const RULES: bool>(term: Term, bindings: W<Indexed>, html: bool) -> IRExpr {
        let mut owned_linked = Vec::new();
        let params = bindings.borrow().params.iter().map(|b|
            IRDecl { name: b.borrow().name.clone(), typ: None, equations: Vec::new() }).collect();
        let lets = bindings.borrow().lets.iter().map(|b|
            IRDecl { name: b.borrow().name.clone(), typ: None, equations: Vec::new() }).collect();
        let goal_rules = term.base.borrow().typ.as_ref().map(|typ| get_rules(&typ.codomain())).unwrap_or_default();
        // TODO special WHNF that does not get stuck and does not unfold definitions
        IRExpr { params, lets, spine: IRSpine::from_body::<RULES>(term.whnf::<RULES, ()>(&mut owned_linked, &mut (), false), html), goal_rules }
    }
}

impl fmt::Display for IRSpine {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.head)?;
        for t in &self.args {
            if t.params.is_empty() && t.lets.is_empty() && t.spine.args.is_empty() {
                write!(f, " {}", t)?;
            } else {
                write!(f, " ({})", t)?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for IRExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.params.is_empty() || !self.lets.is_empty() {
            write!(f, "λ")?;
            for v in &self.params {
                write!(f, " {}", v.name)?;
            }
            for d in &self.lets {
                write!(f, ", {} := {:?}", d.name, d.equations)?;
            }
            write!(f, " ↦ ")?;
        }
        write!(f, "{}", self.spine)
    }
}

/// Displays an `IRExpr` as a Π-type rather than a λ-term.
pub struct AsType<'a>(pub &'a IRExpr);

impl fmt::Display for AsType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt_type(f, "\n")
    }
}

impl IRExpr {
    fn fmt_type(&self, f: &mut fmt::Formatter, sep: &str) -> fmt::Result {
        for d in &self.params {
            write!(f, "({} : ", d.name)?;
            match &d.typ {
                Some(t) => t.fmt_type(f, " ")?,
                None => write!(f, "*")?
            }
            write!(f, ") →{}", sep)?;
        }

        for d in &self.lets {
            write!(f, "({} : ", d.name)?;
            match &d.typ {
                Some(t) => t.fmt_type(f, " ")?,
                None => write!(f, "*")?
            }
            write!(f, " := {:?}) →{}", d.equations, sep)?;
        }

        write!(f, "{}", self.spine)
    }
}

impl IRDecl {
    /// Save this `IRDecl` as JSON to `file`.
    pub fn save(&self, file: String) {
        let file = File::create(file).unwrap();
        serde_json::to_writer(file, self).unwrap();
    }

    /// Load an `IRDecl` from a JSON `file`.
    pub fn load(file: String) -> IRDecl {
        let file = File::open(file).unwrap();
        serde_json::from_reader(file).unwrap()
    }
}

impl fmt::Debug for IREquation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ↦ {}", self.lhs, self.rhs)
    }
}