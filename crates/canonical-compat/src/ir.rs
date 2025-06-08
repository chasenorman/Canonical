use canonical_core::core::*;
use canonical_core::memory::{S, W, WVec};
use canonical_core::search::test;
use std::fmt;
use serde::{Serialize, Deserialize};
use std::fs::File;
use string_interner::{DefaultBackend, StringInterner};
use std::sync::Mutex;
use std::sync::LazyLock;
use crate::reduction::to_rules;
use canonical_core::stats::SearchInfo;

/// We use String interning for the names of inductive types in the `Value`, for fast equality checking.
static INTERNER : LazyLock<Mutex<StringInterner<DefaultBackend>>> = LazyLock::new(|| Mutex::new(StringInterner::default()));

/// A variable with a `name`, and whether it is proof `irrelevant` (unused).
#[derive(PartialEq, Eq, Serialize, Deserialize, Clone)]
pub struct IRVar {
    pub name: String,
    pub irrelevant: bool,
}

#[derive(PartialEq, Eq, Serialize, Deserialize)]
pub struct IRRule {
    pub lhs: IRTerm,
    pub rhs: IRTerm
}

/// A let declaration, with a variable and value. -/
#[derive(PartialEq, Eq, Serialize, Deserialize)]
pub struct IRLet {
    pub var: IRVar,
    pub rules: Vec<IRRule>
}

/// A term is an n-ary, β-normal, η-long λ expression: 
/// `λ params lets . head args`
#[derive(PartialEq, Eq, Serialize, Deserialize)]
pub struct IRTerm {
    pub params: Vec<IRVar>,
    pub lets: Vec<IRLet>,
    pub head: String,
    pub args: Vec<IRTerm>,
}

/// A type is an n-ary Π-type: `Π params lets . codomain`
#[derive(Serialize, Deserialize)]
pub struct IRType {
    pub params: Vec<Option<IRType>>,
    pub lets: Vec<Option<IRType>>,
    pub codomain: IRTerm,
}

impl IRVar {
    pub fn to_bind(&self) -> Bind {
        Bind {
            name: self.name.clone(),
            irrelevant: self.irrelevant,
            rules: Vec::new(),
            owned_bindings: Vec::new()
        }
    }
}

/// Create a `Bind` with the `preferred_name`, appending a suffix such that it is not contained in `es`.
fn disambiguate_bind(preferred_name: &String, es: &ES) -> Bind {
    let mut count = 0;
    let mut name = preferred_name.clone();
    while es.index_of( &name).is_some() {
        count += 1;
        name = preferred_name.clone() + &count.to_string();
    }
    Bind { name, irrelevant: false, rules: Vec::new(), owned_bindings: Vec::new() }
}

/// Construct a copy of `bindings` such that the names are not already in `es`.
fn disambiguate(bindings: W<Indexed<S<Bind>>>, es: &ES) -> Indexed<S<Bind>> {
    let params = bindings.borrow().params.iter().map(
        |b| S::new(disambiguate_bind(&b.borrow().name, es))).collect();
    let lets = bindings.borrow().lets.iter().map(
        |b| S::new(disambiguate_bind(&b.borrow().name, es))).collect();
    Indexed { params, lets }
}

impl IRTerm {
    /// Return a version of `es` with `self.lets` and `params`.
    pub fn extend_es(&self, es: &ES, owned_linked: &mut Vec<S<Linked>>, params: &[IRVar]) -> (ES, S<Indexed<S<Bind>>>) {
        let mut bindings = S::new(Indexed {
            params: params.iter().map(|v| S::new(v.to_bind())).collect(),
            lets: self.lets.iter().map(|d| S::new(d.var.to_bind())).collect()
        });

        let node = Node { 
            entry: Entry { params_id: next_u64(), lets_id: next_u64(), subst: None, context: None }, 
            bindings: bindings.downgrade() 
        };
        let es = es.append(node, owned_linked);

        // Use the extended ES to resolve the values of the lets. 
        for (i, d) in self.lets.iter().enumerate() {
            let mut owned_bindings = Vec::new();
            bindings.borrow_mut().lets[i].borrow_mut().rules = to_rules(&d.rules, &es, owned_linked, &mut owned_bindings);
            bindings.borrow_mut().lets[i].borrow_mut().owned_bindings = owned_bindings;
        }
        (es, bindings)
    }

    pub fn to_term(&self, es: &ES) -> Meta {
        let mut owned_linked = Vec::new();
        let (es, bindings) = self.extend_es(es, &mut owned_linked, &self.params);
        self.to_body(es, bindings, owned_linked)
    }

    /// Finds the head `DeBruijnIndex` in the `es` and creates a Meta with `bindings` and recursively converted arguments.
    fn to_body(&self, es: ES, bindings: S<Indexed<S<Bind>>>, owned_linked: Vec<S<Linked>>) -> Meta {
        let (head, bind) = es.index_of(&self.head).unwrap();
        let args = self.args.iter().map(|t| S::new(t.to_term(&es))).collect();
 
        Meta {
            assignment: Some(Assignment { head, args, bind, changes: Vec::new(), _owned_linked: owned_linked, has_rigid_type: true }),
            typ: None,
            gamma: es,
            equations: Vec::new(),
            bindings: bindings.downgrade(),
            _owned_bindings: Some(bindings),
            stats: SearchInfo::new(),
            stats_buffer: SearchInfo::new(),
            has_rigid_equation: false,
            branching: 1.0,
            parent: None,
        }
    }

    pub fn from_term(meta: W<Meta>, es: &ES) -> IRTerm {
        let entry = Entry { params_id: next_u64(), lets_id: next_u64(), subst: None, context: None };
        let mut owned_linked = Vec::new();
        let bindings: S<Indexed<S<Bind>>> = S::new(disambiguate(meta.borrow().bindings.clone(), es));
        let node = Node { entry , bindings: bindings.downgrade() };
        let es = es.append(node, &mut owned_linked);
        let params = bindings.borrow().params.iter().map(|b| IRVar { name: b.borrow().name.clone(), irrelevant: false }).collect();
        let lets = bindings.borrow().lets.iter().map(|b| 
            IRLet { var: IRVar { name: b.borrow().name.clone(), irrelevant: false }, rules: Vec::new() }).collect();
        match &meta.borrow().assignment {
            None => IRTerm { params, lets, head: Self::meta_html(meta), args: Vec::new() },
            Some(assignment) => IRTerm {
                params, lets,
                head: es.sub_es(assignment.head.0).get_var(assignment.head.1).bind.borrow().name.clone(),
                args: meta.borrow().assignment.as_ref().unwrap().args.iter().map(|m| IRTerm::from_term(m.downgrade(), &es)).collect()
            }
        }
    }

    fn meta_html(meta: W<Meta>) -> String {
        let varname = "?".to_string() + &meta.borrow().typ.as_ref().unwrap().2.borrow().name;
        let meta_id = meta.borrow() as *const Meta as usize;

        let options = meta.borrow().gamma.iter().filter_map(|(db, linked)| {
            // TODO properly set program synthesis
            if let Some(Some(result)) = test(db, linked, meta.clone(), false) {
                let name = result.0.bind.borrow().name.clone();

                let (index, def) = match db.1 {
                    Index::Param(i) => (i, false),
                    Index::Let(i) => (i, true)
                };
                let debruijn = db.0.0;
                
                return Some(format!("<button class='option' onclick='assign({meta_id}, {debruijn}, {index}, {def})'>{name}</button>"));
            }
            None
        }).reduce(|a, b| format!("{a}</br>{b}")).unwrap_or_default();

        let tooltiptext = format!("<div class='provers tooltiptext'>{options}</div>");
        let tooltip = format!("<div class='tooltip'><span class='meta'>{varname}</span>{tooltiptext}</div>");
        return format!("<label><input type='radio' name='meta' id='{meta_id}' value='{meta_id}'>{tooltip}</label>")
    }
}

impl IRType {
    pub fn to_type(&self, es: &ES) -> TypeBase {
        let codomain = self.codomain.to_term(es);

        let params : Vec<Option<S<TypeBase>>> = self.params.iter().map(|t| 
            t.as_ref().map(|t| S::new(t.to_type(&codomain.gamma)))).collect();
        let mut lets : Vec<Option<S<TypeBase>>> = self.lets.iter().map(|t|
             t.as_ref().map(|t| S::new(t.to_type(&codomain.gamma)))).collect();

        TypeBase {
            codomain: S::new(codomain),
            types: S::new(Indexed { params, lets })
        }
    }
}

impl fmt::Display for IRTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.params.is_empty() || !self.lets.is_empty() {
            write!(f, "λ")?;
            for v in &self.params {
                write!(f, " {}", v.name)?;
            }
            for d in &self.lets {
                write!(f, ", {} := {:?}", d.var.name, d.rules)?;
            }
            write!(f, " ↦ ")?;
        }
        write!(f, "{}", self.head)?;
        for t in &self.args {
            if t.params.is_empty() && t.lets.is_empty() && t.args.is_empty() {
                write!(f, " {}", t)?;
            } else {
                write!(f, " ({})", t)?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for IRType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt(f, "\n")
    }
}

impl IRType {
    fn fmt(&self, f: &mut fmt::Formatter, sep: &str) -> fmt::Result {
        for (typ, var) in self.params.iter().zip(self.codomain.params.iter()) {
            write!(f, "({} : ", var.name)?;
            match &typ {
                Some(t) => t.fmt(f, " ")?,
                None => write!(f, "*")?
            }
            write!(f, ") →{}", sep)?;
        }
        
        for (typ, def) in self.lets.iter().zip(self.codomain.lets.iter()) {
            write!(f, "({} : ", def.var.name)?;
            match &typ {
                Some(t) => t.fmt(f, " ")?,
                None => write!(f, "*")?
            }
            write!(f, " := {:?}) →{}", def.rules, sep)?;
        }

        write!(f, "{}", self.codomain.head)?;

        for t in &self.codomain.args {
            if t.params.is_empty() && t.lets.is_empty() && t.args.is_empty() {
                write!(f, " {}", t)?;
            } else {
                write!(f, " ({})", t)?;
            }
        }
        Ok(())
    }
}

impl IRType {
    /// Save this `IRType` as JSON to `file`.
    pub fn save(&self, file: String) {
        let file = File::create(file).unwrap();
        serde_json::to_writer(file, self).unwrap();
    }

    /// Load an `IRType` from a JSON `file`.
    pub fn load(file: String) -> IRType {
        let file = File::open(file).unwrap();
        serde_json::from_reader(file).unwrap()
    }
}

impl fmt::Debug for IRRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ↦ {}", self.lhs, self.rhs)
    }
}