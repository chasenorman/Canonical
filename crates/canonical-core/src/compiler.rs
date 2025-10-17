use crate::core::*;
use crate::memory::*;

#[derive(Clone, Copy)]
enum Polarity { Goal, Premise }

fn get_type(term: Term, owned_linked: &mut Vec<S<Linked>>) -> Option<Term> {
    let assn = term.base.borrow().assignment.as_ref().unwrap();
    let sub_es = term.es.sub_es(assn.head.0);
    let context = sub_es.linked.as_ref().unwrap().borrow().node.entry.context.as_ref().unwrap();
    if let Some(tb) = context.0.borrow().types.borrow()[assn.head.1].as_ref() {
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

pub fn compile(typ: Type) {
    let mut premises = Vec::new();
    let mut goals = Vec::new();
    let mut owned_linked = Vec::new();
    let mut owned_metas = Vec::new();
    get_compilation_info(typ, &mut premises, &mut goals, Polarity::Goal, &mut owned_linked, &mut owned_metas);
    println!("{:?}", premises.iter().map(|typ| typ.to_string()).collect::<Vec<_>>());
    println!("{:?}", goals.iter().map(|typ| typ.to_string()).collect::<Vec<_>>());
    let mut count: u32 = 0;
    for goal in goals.iter() {
        for premise in premises.iter() {
            let success = unify(goal.codomain(), premise.codomain(), 0);
            if success {
                count += 1;
            }
            println!("{} <- {}: {}", goal.2.borrow().name, premise.2.borrow().name, success);
        }
    }
    println!("Total unifications: {} / {}", count, goals.len() * premises.len());
}

fn opposite(polarity: Polarity) -> Polarity {
    match polarity {
        Polarity::Goal => Polarity::Premise,
        Polarity::Premise => Polarity::Goal
    }
}

fn length(es: ES) -> u32 {
    let mut len = 0;
    let mut current = es.linked.clone();
    while let Some(linked) = current {
        len += 1;
        current = linked.borrow().tail.clone();
    }
    len
}

fn get_compilation_info(typ: Type, premises: &mut Vec<Type>, goals: &mut Vec<Type>, 
    polarity: Polarity, owned_linked: &mut Vec<S<Linked>>, owned_metas: &mut Vec<Vec<S<Meta>>>) {
    match polarity {
        Polarity::Goal => {
            let es = typ.1.append(Node { entry: Entry {
                params_id: next_u64(), lets_id: next_u64(), subst: None, 
                context: Some(typ.clone())
            }, bindings: typ.0.borrow().codomain.borrow().bindings.clone() }, owned_linked);
            for i in Indexed::iter(typ.0.borrow().types.downgrade()) {
                if let Some(child) = typ.0.borrow().types.borrow()[i].as_ref() {
                    get_compilation_info(Type(child.downgrade(), es.clone(), typ.0.borrow().codomain.borrow().bindings.borrow()[i].downgrade()), premises, goals, Polarity::Premise, owned_linked, owned_metas)
                }
            }
            goals.push(Type(typ.0.clone(), es, typ.2.clone()));
        },
        Polarity::Premise => {
            let metas = typ.0.borrow().args_metas(None);
            let es = typ.1.append(Node { entry: Entry {
                params_id: next_u64(), lets_id: next_u64(),
                subst: Some(Subst(WVec::new(&metas), ES::new())),
                context: Some(typ.clone())
            }, bindings: typ.0.borrow().codomain.borrow().bindings.clone() }, owned_linked);
            owned_metas.push(metas);
            for i in Indexed::iter(typ.0.borrow().types.downgrade()) {
                if let Some(child) = typ.0.borrow().types.borrow()[i].as_ref() {
                    get_compilation_info(Type(child.downgrade(), es.clone(), typ.0.borrow().codomain.borrow().bindings.borrow()[i].downgrade()), premises, goals, Polarity::Goal, owned_linked, owned_metas)
                }
            }
            premises.push(Type(typ.0.clone(), es, typ.2.clone()));
        }
    }
}