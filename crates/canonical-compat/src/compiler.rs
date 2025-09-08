use crate::*;
use canonical_core::memory::*;

enum Polarity { Goal, Premise }
struct CompilationInfo {
    name: String,
    optimistic_es: ES
}

fn get_type(term: Term, owned_linked: &mut Vec<S<Linked>>) -> Option<Term> {
    let assn = term.base.borrow().assignment.as_ref().unwrap();
    let sub_es = term.es.sub_es(assn.head.0);
    let context = sub_es.linked.as_ref().unwrap().borrow().node.entry.context.as_ref().unwrap();
    if let Some(tb) = context.0.borrow()[assn.head.1].as_ref() {
        Some(Term {
            base: tb.borrow().codomain.downgrade(),
            es: sub_es.append(Node { 
              entry: Entry::subst(Subst(WVec::new(&assn.args), term.es.clone())), 
              bindings: tb.borrow().codomain.borrow().bindings.clone()
            }, owned_linked)
        })
    } else {
        None
    }
}

pub fn unify(goal: Term, premise: Term, depth: u32) -> bool {
    if depth > 1 { return true }
    let mut owned_linked = Vec::new();
    // println!("Unify depth {}: {:} = {:}", depth, goal.whnf::<true, ()>(&mut owned_linked, &mut ()), 
        // premise.whnf::<true, ()>(&mut owned_linked, &mut ()));
    let eq = Equation { goal: goal.clone(), premise: premise.clone() };
    let success = eq.reduce(&mut Vec::new(), &mut Vec::new(), &mut Vec::new());
    if !success { return false; }
    match (get_type(goal, &mut owned_linked), get_type(premise, &mut owned_linked)) {
        (Some(goal), Some(premise)) => return unify(goal, premise, depth + 1),
        (None, None) => return true,
        _ => return false
    }
}

pub fn compile(typ: &mut TypeBase) {
    let mut premises = Vec::new();
    let mut goals = Vec::new();
    let mut owned_linked = Vec::new();
    let mut owned_metas = Vec::new();
    get_compilation_info(typ, &mut premises, &mut goals, ES::new(), Polarity::Goal, &mut owned_linked, &mut owned_metas, "proof".to_string());
    println!("{:?}", premises.iter().map(|(_, info)| &info.name).collect::<Vec<_>>());
    println!("{:?}", goals.iter().map(|(_, info)| &info.name).collect::<Vec<_>>());
    let mut count: u32 = 0;
    for goal in goals.iter() {
        for premise in premises.iter() {
            let success = unify(Term { base: goal.0.codomain.downgrade(), es: goal.1.optimistic_es.clone() }, 
                                Term { base: premise.0.codomain.downgrade(), es: premise.1.optimistic_es.clone() }, 0);
            if success {
                count += 1;
            }
            println!("{} <- {}: {}", goal.1.name, premise.1.name, success);
        }
    }
    println!("Total unifications: {} / {}", count, goals.len() * premises.len());
}

fn get_compilation_info<'a>(typ: &'a TypeBase, premises: &mut Vec<(&'a TypeBase, CompilationInfo)>, goals: &mut Vec<(&'a TypeBase, CompilationInfo)>, 
    es: ES, polarity: Polarity, owned_linked: &mut Vec<S<Linked>>, owned_metas: &mut Vec<Vec<S<Meta>>>, name: String) {
    match polarity {
        Polarity::Goal => {
            let es = es.append(Node { entry: Entry {
                params_id: next_u64(), lets_id: next_u64(), subst: None, 
                context: Some(Context(typ.types.downgrade(), es.clone(), typ.codomain.borrow().bindings.clone()))
            }, bindings: typ.codomain.borrow().bindings.clone() }, owned_linked);
            for i in Indexed::iter(typ.types.downgrade()) {
                if let Some(child) = typ.types.borrow()[i].as_ref() {
                    get_compilation_info(child.borrow(), premises, goals, es.clone(), Polarity::Premise, owned_linked, owned_metas, 
                        typ.codomain.borrow().bindings.borrow()[i].borrow().name.clone())
                }
            }
            goals.push((typ, CompilationInfo { optimistic_es: es, name }));
        },
        Polarity::Premise => {
            let metas = typ.args_metas(None);
            let es = es.append(Node { entry: Entry {
                params_id: next_u64(), lets_id: next_u64(),
                subst: Some(Subst(WVec::new(&metas), ES::new())),
                context: Some(Context(typ.types.downgrade(), es.clone(), typ.codomain.borrow().bindings.clone()))
            }, bindings: typ.codomain.borrow().bindings.clone() }, owned_linked);
            owned_metas.push(metas);
            for i in Indexed::iter(typ.types.downgrade()) {
                if let Some(child) = typ.types.borrow()[i].as_ref() {
                    get_compilation_info(child.borrow(), premises, goals, es.clone(), Polarity::Goal, owned_linked, owned_metas, 
                        typ.codomain.borrow().bindings.borrow()[i].borrow().name.clone())
                }
            }
            premises.push((typ, CompilationInfo { optimistic_es: es, name }));
        }
    }
}