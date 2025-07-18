use crate::*;
use canonical_core::memory::*;
use std::collections::{HashMap, HashSet};

struct Build {
    pub pattern: Vec<Option<Symbol>>,
    pub arguments: HashSet<String>
}

impl IRTerm {
    /// Determines the variables that are unbound in an IRTerm.
    pub fn free_variables(&self, es: &ES, result: &mut HashSet<String>) {
        let mut owned_linked = Vec::new();
        // This function just returns strings, so the bindings don't need to be saved.
        let (es, _bindings) = self.add_local(es, &mut owned_linked);

        if es.index_of(&self.head).is_none() {
            result.insert(self.head.clone());
        }

        for arg in &self.args {
            arg.free_variables(&es, result);
        }
    }
}

/// For a vector `builds` that agree on a head symbol, this function determines
/// the number of non-wildcard head symbols and the number of distinct head symbols
/// that occur at argument `i` of each `Build`.
fn head_count(i: usize, builds: &Vec<(&mut Build, &IRTerm, ES)>) -> (u32, u32) {
    let mut owned_linked = Vec::new();
    let mut non_wildcards = 0;
    let mut distinct = 0;
    let mut seen = HashSet::new();
    for (_, term, es) in builds.iter() {
        let arg = &term.args[i];
        // This function just returns (u32, u32), so the bindings don't need to be saved.
        let (es, _bindings) = arg.add_local(&es, &mut owned_linked);
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

/// Selects the most efficient ordering of arguments for a vector
/// `builds` which agree on a head symbol. Efficient orderings eliminate
/// candidate patterns as quickly as possible, and do not include arguments
/// that consist of wildcards in all patterns.
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

/// If none of the arguments of `term` are the arguments of `build`, then empty bindings.
/// Otherwise, bindings where the arguments have the appropriate name to be captured.
fn get_bindings(build: &mut Build, term: &IRTerm, es: ES) -> S<Indexed<S<Bind>>> {
    let mut params: Vec<S<Bind>> = Vec::new();
    let mut found = false;
    
    for arg in term.args.iter() {
        let mut owned_linked = Vec::new();
        let (es, _bindings) = arg.add_local(&es, &mut owned_linked);
        if es.index_of(&arg.head).is_none() && build.arguments.contains(&arg.head) {
            build.arguments.remove(&arg.head);
            params.push(S::new(Bind::new(arg.head.clone())));
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

    // For each head symbol,
    for (bind, mut builds) in map.into_iter() {
        // select an ordering of the arguments,
        let children: Vec<usize> = get_children(&builds);

        // add symbols to each `build` indicating the head symbol and whether the arguments should be captured,
        for (build, term, es) in builds.iter_mut() {
            let bindings = get_bindings(build, term, es.clone());
            
            build.pattern.push(Some(Symbol {
                bind: bind.clone(), 
                children: children.clone(), 
                bindings
            }));
        }

        // and recurse on the arguments.
        for i in children.into_iter() {
            let mut new_builds: Vec<(&mut Build, &IRTerm, ES)> = Vec::new();
            for (build, term, es) in builds.iter_mut() {
                new_builds.push((build, &term.args[i], es.clone()));
            }
            _to_rules(new_builds, owned_linked, owned_bindings);
        }
    }
}

/// Converts a vector of `IRRule` into a vector of `Rule`.
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

    let state: Vec<(&mut Build, &IRTerm, ES)> = owned.iter_mut().zip(rules.iter()).map(|(build, rule)| {
        (build, &rule.lhs, es.clone())
    }).collect();

    _to_rules(state, owned_linked, owned_bindings);

    owned.into_iter().zip(rules.iter()).map(|(mut build, rule)| {
        // Construct the `ES` under which `rhs` will be evaluated.
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
            replacement: S::new(rule.rhs.to_term(&rhs_es)),
            attribution: rule.attribution.clone()
        }
    }).collect()
}


fn to_redex(term: &IRTerm, es: &ES, build: &mut Vec<Instruction>) {
    if let Some((_, bind)) = es.index_of(&term.head) {
        build.push(Instruction {
            bind: bind.clone(),
            parents: 0,
            child: 0  
        });
        for (i, arg) in term.args.iter().enumerate() {
            to_redex(arg, es, build);
            build.last_mut().unwrap().child = i + 1;
        }
        build.last_mut().unwrap().parents += 1;
    }
}

/// Filters `IRRules` that are redexes, and converts them to `Vec<Instruction>`.
pub fn to_redexes(rules: &Vec<IRRule>, es: &ES) -> Vec<Vec<Instruction>> {
    rules.iter().filter_map(|rule| {
        rule.is_redex.then(|| {
            let mut build: Vec<Instruction> = Vec::new();
            to_redex(&rule.lhs, es, &mut build);
            build
        })
    }).collect()
}