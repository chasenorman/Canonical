use crate::*;
use canonical_core::core::*;
use canonical_core::memory::*;
use std::collections::{HashMap, HashSet};

struct Build {
    pub pattern: Vec<Option<Symbol>>,
    pub bindings: Vec<W<Indexed<S<Bind>>>>,
    pub arguments: HashSet<String>
}

impl IRTerm {
    pub fn add_local(&self, es: &ES) -> ES {
        let bindings = S::new(Indexed {
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

fn get_entries(build: &mut Build, term: &IRTerm, es: ES) -> Vec<SubstRange> {
    let mut entries = Vec::new();
    let mut bindings: Option<Indexed<S<Bind>>> = None;
    let mut start = 0;
    
    for (i, arg) in term.args.iter().enumerate() {
        if arg.add_local(&es).index_of(&arg.head).is_none() && build.arguments.contains(&arg.head) {
            build.arguments.remove(&arg.head);
            if bindings.is_none() {
                bindings = Some(Indexed {
                    params: Vec::new(),
                    lets: Vec::new()
                });
                start = i;
            }
            // TODO add simple constructor
            bindings.as_mut().unwrap().params.push(S::new(Bind {
                name: arg.head.clone(),
                irrelevant: false,
                rules: Vec::new(),
                value: Value::Opaque,
                major: false
            }))
        } else if bindings.is_some() {
            let bindings = S::new(bindings.take().unwrap());
            build.bindings.push(bindings.downgrade());
            entries.push(SubstRange{ range: start..i, bindings });
        }
    }

    if bindings.is_some() {
        let bindings = S::new(bindings.take().unwrap());
        build.bindings.push(bindings.downgrade());
        entries.push(SubstRange{ range: start..term.args.len(), bindings });
    }

    return entries;
}

fn _to_rules(state: Vec<(&mut Build, &IRTerm, ES)>) {
    // Partition by the head `Bind`.
    let mut map: HashMap<W<Bind>, Vec<(&mut Build, &IRTerm, ES)>> = HashMap::new();
    for (build, term, es) in state.into_iter() {
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

        for (build, term, es) in builds.iter_mut() {
            let entries = get_entries(build, term, es.clone());
            
            build.pattern.push(Some(Symbol {
                bind: bind.clone(), 
                children: children.clone(), 
                entries
            }))
        }

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
        let mut rhs_es = es.clone();
        for bindings in build.bindings.iter() {
            rhs_es = rhs_es.append(Node {
                entry: Entry { 
                    params_id: next_u64(), 
                    lets_id: next_u64(), 
                    subst: None, 
                    context: None 
                }, 
                bindings: bindings.clone()
            }, owned_linked);
        }

        Rule {
            pattern: build.pattern, // TODO remove trailing wildcards
            replacement: S::new(rule.rhs.to_term(&rhs_es)),
        }
    }).collect()
}