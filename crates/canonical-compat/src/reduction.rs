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
    pub fn add_local(&self, es: &ES, owned_linked: &mut Vec<S<Linked>>) -> (ES, S<Indexed<S<Bind>>>) {
        let bindings = S::new(Indexed {
            params: self.params.iter().map(|v| S::new(v.to_bind())).collect(),
            lets: self.lets.iter().map(|d| S::new(d.var.to_bind())).collect()
        });

        let node = Node { 
            entry: Entry { params_id: next_u64(), lets_id: next_u64(), subst: None, context: None }, 
            bindings: bindings.downgrade() 
        };
        (es.append(node, owned_linked), bindings)
    }

    pub fn free_variables(&self, es: &ES, result: &mut HashSet<String>) {
        let mut owned_linked = Vec::new();
        // This function just returns strings, so the bindings don't need to be saved.
        let (es, bindings) = self.add_local(es, &mut owned_linked);

        if es.index_of(&self.head).is_none() {
            result.insert(self.head.clone());
        }

        for arg in &self.args {
            arg.free_variables(&es, result);
        }
    }
}

fn head_count(i: usize, builds: &Vec<(&mut Build, &IRTerm, ES)>) -> (u32, u32) {
    let mut owned_linked = Vec::new();
    let mut non_wildcards = 0;
    let mut distinct = 0;
    let mut seen = HashSet::new();
    for (_, term, es) in builds.iter() {
        let arg = &term.args[i];
        // This function just returns (u32, u32), so the bindings don't need to be saved.
        let (es, bindings) = arg.add_local(&es, &mut owned_linked);
        if let Some((_, bind)) = es.index_of(&arg.head) {
            if !seen.contains(&bind) {
                distinct += 1;
            }
            seen.insert(bind.clone());
            non_wildcards += 1;
        }
    }
    (non_wildcards, distinct)
}

fn get_children(builds: &Vec<(&mut Build, &IRTerm, ES)>) -> Vec<usize> {
    let len = builds[0].1.args.len();
    let mut children: Vec<usize> = (0..len).filter(|&i| {
        head_count(i, builds).0 != 0
    }).collect();

    children.sort_by(|&a, &b| {
        let (a_non_wildcards, a_distinct) = head_count(a, builds);
        let (b_non_wildcards, b_distinct) = head_count(b, builds);
        
        // Decreasing order of non-wildcards
        if a_non_wildcards != b_non_wildcards {
            return b_non_wildcards.cmp(&a_non_wildcards);            
        }

        // Increasing order of distinct
        return a_distinct.cmp(&b_distinct)
    });

    return children;
}

fn get_entries(build: &mut Build, term: &IRTerm, es: ES) -> Vec<SubstRange> {
    let mut entries = Vec::new();
    let mut bindings: Option<Indexed<S<Bind>>> = None;
    let mut start = 0;
    
    for (i, arg) in term.args.iter().enumerate() {
        let mut owned_linked = Vec::new();
        let (es, _bindings) = arg.add_local(&es, &mut owned_linked);
        if es.index_of(&arg.head).is_none() && build.arguments.contains(&arg.head) {
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
                major: false,
                owned_bindings: Vec::new()
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

fn _to_rules(state: Vec<(&mut Build, &IRTerm, ES)>, owned_linked: &mut Vec<S<Linked>>, owned_bindings: &mut Vec<S<Indexed<S<Bind>>>>) {
    // Partition by the head `Bind`.
    let mut map: HashMap<W<Bind>, Vec<(&mut Build, &IRTerm, ES)>> = HashMap::new();
    for (build, term, es) in state.into_iter() {
        let (es, bindings) = term.add_local(&es, owned_linked);
        owned_bindings.push(bindings);
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
                new_builds.push((build, &term.args[i], es.clone()));
            }
            _to_rules(new_builds, owned_linked, owned_bindings);
        }
    }
}

pub fn to_rules(rules: &Vec<IRRule>, es: &ES, owned_linked: &mut Vec<S<Linked>>, owned_bindings: &mut Vec<S<Indexed<S<Bind>>>>) -> Vec<Rule> {    
    let mut owned: Vec<Build> = rules.iter().map(|rule|{
        let mut arguments: HashSet<String> = HashSet::new();
        // TODO ensure that params are set to Vec::new()
        rule.rhs.free_variables(es, &mut arguments);
        Build {
            pattern: Vec::new(),
            bindings: Vec::new(),
            arguments
        }
    }).collect();

    let state: Vec<(&mut Build, &IRTerm, ES)> = owned.iter_mut().zip(rules.iter()).map(|(build, rule)| {
        (build, &rule.lhs, es.clone())
    }).collect();

    _to_rules(state, owned_linked, owned_bindings);

    owned.into_iter().zip(rules.iter()).map(|(mut build, rule)| {
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

        while let Some(None) = build.pattern.last() {
            build.pattern.pop();
        }

        Rule {
            pattern: build.pattern,
            replacement: S::new(rule.rhs.to_term(&rhs_es)),
        }
    }).collect()
}