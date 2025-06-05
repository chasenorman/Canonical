use crate::*;
use canonical_core::core::*;
use canonical_core::memory::*;
use std::collections::{HashMap, HashSet};

struct Build {
    pub pattern: Vec<Option<Symbol>>,
    pub bindings: Vec<Indexed<S<Bind>>>,
    pub arguments: HashSet<String>
}

impl IRTerm {
    pub fn add_local(&self, es: &ES) -> ES {
        let mut bindings = S::new(Indexed {
            params: self.params.iter().map(|v| S::new(v.to_bind())).collect(),
            lets: self.lets.iter().map(|d| S::new(d.var.to_bind())).collect()
        });

        let node = Node { 
            entry: Entry { params_id: next_u64(), lets_id: next_u64(), subst: None, context: None }, 
            bindings: bindings.downgrade() 
        };
        es.append(node, &mut Vec::new())
    }

    pub fn free_variables(&self, es: &ES, owned_linked: &mut Vec<S<Linked>>, result: &mut HashSet<String>) {
        let es = self.add_local(es);

        if es.index_of(&self.head).is_none() {
            result.insert(self.head.clone());
        }

        for arg in &self.args {
            arg.free_variables(&es, owned_linked, result);
        }
    }
}

fn get_children(builds: &Vec<(&mut Build, &IRTerm, ES)>) -> Vec<usize> {
    let len = builds.get(0).unwrap().1.args.len();
    let mut children: Vec<usize> = Vec::new();
    for i in 0..len {
        children.push(i);
    }
    // TODO 
    return children;
}

fn _to_rules(state: Vec<(&mut Build, &IRTerm, ES)>) {
    // Partition by the head `Bind`.
    let mut map: HashMap<W<Bind>, Vec<(&mut Build, &IRTerm, ES)>> = HashMap::new();
    for (mut build, term, es) in state.into_iter() {
        let es = term.add_local(&es);
        if let Some((_, bind)) = es.index_of(&term.head) {
            if !map.contains_key(&bind) {
                map.insert(bind.clone(), Vec::new());
            }
            map.get_mut(&bind).unwrap().push((build, term, es));
        } else {
            build.pattern.push(None);
        }
    }

    for (bind, mut builds) in map.into_iter() {
        let children: Vec<usize> = get_children(&builds);

        for (build, _, _) in builds.iter_mut() {
            build.pattern.push(Some(Symbol {
                bind: bind.clone(), 
                children: children.clone(), 
                entries: Vec::new()
            }))
        }

        // TODO entries
        for i in children.into_iter() {
            let mut new_builds: Vec<(&mut Build, &IRTerm, ES)> = Vec::new();
            for (build, term, es) in builds.iter_mut() {
                let arg = term.args.get(i).unwrap();
                new_builds.push((build, arg, es.clone()));
            }
            _to_rules(new_builds);
        }
    }
}

pub fn to_rules(rules: &Vec<IRRule>, es: &ES, owned_linked: &mut Vec<S<Linked>>) -> Vec<Rule> {
    let mut owned: Vec<Build> = rules.iter().map(|rule|{
        let mut arguments: HashSet<String> = HashSet::new();
        // TODO ensure that params are set to Vec::new()
        rule.rhs.free_variables(es, owned_linked, &mut arguments);
        Build {
            pattern: Vec::new(),
            bindings: Vec::new(),
            arguments
        }
    }).collect();

    let state: Vec<(&mut Build, &IRTerm, ES)> = owned.iter_mut().zip(rules.iter()).map(|(build, rule)| {
        (build, &rule.lhs, es.clone())
    }).collect();

    _to_rules(state);

    owned.into_iter().zip(rules.iter()).map(|(build, rule)| {
        Rule {
            pattern: build.pattern, // TODO remove trailing wildcards
            replacement: S::new(rule.rhs.to_term(es)), // TODO segment
        }
    }).collect()
}