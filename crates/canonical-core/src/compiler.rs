use crate::core::*;
use crate::memory::*;
use std::sync::{Arc, atomic::{AtomicU32, Ordering}};
use arc_swap::ArcSwap;
use hashbrown::HashMap;
use once_cell::sync::Lazy;

pub static COMPILATION: Lazy<ArcSwap<HashMap<usize, Vec<Index>>>> = Lazy::new(|| ArcSwap::from_pointee(HashMap::new()));

#[derive(Clone, Copy)]
enum Polarity { Goal, Premise }

impl Polarity {
    fn opposite(&self) -> Polarity {
        match self {
            Polarity::Goal => Polarity::Premise,
            Polarity::Premise => Polarity::Goal
        }
    }
}

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
    let mut goals = Vec::new();
    let mut owned_linked = Vec::new();
    let mut owned_metas = Vec::new();
    get_compilation_info(typ, &mut goals, Polarity::Goal, &mut owned_linked, &mut owned_metas);
    // println!("{:?}", goals.iter().map(|(typ, children)| typ.2.name).collect::<Vec<_>>());
    let mut count: u32 = 0;
    for goal in goals.iter() {
        for goal2 in goals.iter() {
            for premise in goal2.1.iter() {
                let success = unify(goal.0.codomain(), premise.0.codomain(), 0);
                if success {
                    count += 1;
                }
                println!("{} <- {}: {}", goal.0.2.borrow().name, premise.0.2.borrow().name, success);
            }
        }
    }
    println!("Total unifications: {}", count);
}

fn get_compilation_info(typ: Type, goals: &mut Vec<(Type, Vec<(Type, Index)>)>, 
    polarity: Polarity, owned_linked: &mut Vec<S<Linked>>, owned_metas: &mut Vec<Vec<S<Meta>>>) -> Type {
    let entry = match polarity {
        Polarity::Goal => Entry {
            params_id: next_u64(), lets_id: next_u64(), subst: None, 
            context: Some(typ.clone())
        },
        Polarity::Premise => {
            let metas = typ.0.borrow().args_metas(None);
            let result = Entry {
                params_id: next_u64(), lets_id: next_u64(),
                subst: Some(Subst(WVec::new(&metas), ES::new())),
                context: Some(typ.clone())
            };
            owned_metas.push(metas);
            result
        }
    };

    let es = typ.1.append(Node { entry: entry, bindings: typ.0.borrow().codomain.borrow().bindings.clone() }, owned_linked);

    let mut children = Vec::new();
    for i in Indexed::iter(typ.0.borrow().types.downgrade()) {
        if let Some(child) = typ.0.borrow().types.borrow()[i].as_ref() {
            let child = get_compilation_info(Type(child.downgrade(), es.clone(), typ.0.borrow().codomain.borrow().bindings.borrow()[i].downgrade()), goals, polarity.opposite(), owned_linked, owned_metas);
            children.push((child, i));
        }
    }

    let typ = Type(typ.0.clone(), es.clone(), typ.2.clone());

    if matches!(polarity, Polarity::Goal) {
        goals.push((typ.clone(), children));
    }

    return typ;
}