use crate::*;
use canonical_core::memory::*;
use std::collections::{HashMap, HashSet};

struct Build {
    pub pattern: Vec<Option<Symbol>>,
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
        self.spine.free_variables(&es, result);
    }
}

impl IRSpine {
    pub fn free_variables(&self, es: &ES, result: &mut HashSet<String>) {
        if es.index_of(&self.head).is_none() {
            result.insert(self.head.clone());
        }

        for arg in &self.args {
            arg.free_variables(es, result);
        }
    }
}

fn head_count(i: usize, builds: &Vec<(&mut Build, &IRSpine, ES)>) -> (u32, u32) {
    let mut owned_linked = Vec::new();
    let mut non_wildcards = 0;
    let mut distinct = 0;
    let mut seen = HashSet::new();
    for (_, term, es) in builds.iter() {
        let arg = &term.args[i];
        // This function just returns (u32, u32), so the bindings don't need to be saved.
        let (es, bindings) = arg.add_local(&es, &mut owned_linked);
        if let Some((_, bind)) = es.index_of(&arg.spine.head) {
            if !seen.contains(&bind) {
                distinct += 1;
            }
            seen.insert(bind.clone());
            non_wildcards += 1;
        }
    }
    (non_wildcards, distinct)
}

fn get_children(builds: &Vec<(&mut Build, &IRSpine, ES)>) -> Vec<usize> {
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

fn get_bindings(build: &mut Build, term: &IRSpine, es: ES) -> S<Indexed<S<Bind>>> {
    let mut params: Vec<S<Bind>> = Vec::new();
    let mut found = false;
    
    for arg in term.args.iter() {
        let mut owned_linked = Vec::new();
        let (es, _bindings) = arg.add_local(&es, &mut owned_linked);
        if es.index_of(&arg.spine.head).is_none() && build.arguments.contains(&arg.spine.head) {
            build.arguments.remove(&arg.spine.head);
            params.push(S::new(Bind::new(arg.spine.head.clone())));
            found = true;
        } else {
            params.push(S::new(Bind::new("*".to_string())));
        }
    }

    return S::new(Indexed {
        params: if found { params } else { Vec::new() },
        lets: Vec::new()
    });
}

fn _to_rules(state: Vec<(&mut Build, &IRSpine, ES)>, owned_linked: &mut Vec<S<Linked>>, owned_bindings: &mut Vec<S<Indexed<S<Bind>>>>) {
    // Partition by the head `Bind`.
    let mut map: HashMap<W<Bind>, Vec<(&mut Build, &IRSpine, ES)>> = HashMap::new();
    for (build, term, es) in state.into_iter() {
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
            let bindings = get_bindings(build, term, es.clone());
            
            build.pattern.push(Some(Symbol {
                bind: bind.clone(), 
                children: children.clone(), 
                bindings
            }));
        }

        for i in children.into_iter() {
            let mut new_builds: Vec<(&mut Build, &IRSpine, ES)> = Vec::new();
            for (build, term, es) in builds.iter_mut() {
                let (es, bindings) = term.args[i].add_local(&es, owned_linked);
                owned_bindings.push(bindings);
                new_builds.push((build, &term.args[i].spine, es));
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
            arguments
        }
    }).collect();

    let state: Vec<(&mut Build, &IRSpine, ES)> = owned.iter_mut().zip(rules.iter()).map(|(build, rule)| {
        (build, &rule.lhs, es.clone())
    }).collect();

    _to_rules(state, owned_linked, owned_bindings);

    owned.into_iter().zip(rules.iter()).map(|(mut build, rule)| {
        let mut rhs_es = es.clone();
        for symbol in build.pattern.iter() {
            if let Some(symbol) = symbol {
                rhs_es = rhs_es.append(Node {
                    entry: Entry { 
                        params_id: next_u64(), 
                        lets_id: next_u64(), 
                        subst: None, 
                        context: None 
                    }, 
                    bindings: symbol.bindings.downgrade()
                }, owned_linked);
            }
        }

        while let Some(None) = build.pattern.last() {
            build.pattern.pop();
        }

        Rule {
            pattern: build.pattern,
            replacement: S::new(rule.rhs.to_body(rhs_es, S::new(Indexed { params: Vec::new(), lets: Vec::new() }), Vec::new())),
            attribution: rule.attribution.clone()
        }
    }).collect()
}


fn to_redex(term: &IRSpine, es: &ES, build: &mut Vec<Instruction>) {
    if let Some((_, bind)) = es.index_of(&term.head) {
        build.push(Instruction {
            bind: bind.clone(),
            parents: 0,
            child: 0  
        });
        for (i, arg) in term.args.iter().enumerate() {
            to_redex(&arg.spine, es, build);
            build.last_mut().unwrap().child = i + 1;
        }
        build.last_mut().unwrap().parents += 1;
    }
}


pub fn to_redexes(rules: &Vec<IRRule>, es: &ES) -> Vec<Vec<Instruction>> {
    rules.iter().filter_map(|rule| {
        rule.is_redex.then(|| {
            let mut build: Vec<Instruction> = Vec::new();
            to_redex(&rule.lhs, es, &mut build);
            build
        })
    }).collect()
}