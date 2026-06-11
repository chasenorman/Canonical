use std::collections::HashMap;
use std::fs::File;
use crate::ir::*;
use canonical_core::core::Bind;
use canonical_core::compiler::{GOALS, PREMISES};
use canonical_core::memory::W;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct Example {
    /// The top-level name of the problem.
    pub name: String,
    pub problem: IRType,
    pub unifications: HashMap<String, HashMap<String, u32>>,
    pub tokens: Vec<Token>,
    pub binds: HashMap<String, Vec<Position>>,
    /// The names of the binds at goal polarity: the outer keys of `unifications`.
    pub goals: Vec<String>,
    /// The names of the binds at premise polarity: the inner keys of `unifications`.
    pub premises: Vec<String>
}

impl Example {
    /// Construct an `Example` for the most recently compiled problem:
    /// `goals` and `premises` are read from the statics populated by `compile`.
    pub fn new(name: String, problem: IRType, unifications: HashMap<String, HashMap<String, u32>>,
            binds: &HashMap<W<Bind>, Vec<Position>>, tokens: Vec<Token>) -> Example {
        Example {
            name,
            problem,
            unifications,
            tokens,
            binds: binds.iter().map(|(b, p)| (b.borrow().name.clone(), p.clone())).collect(),
            goals: GOALS.load().as_ref().clone(),
            premises: PREMISES.load().as_ref().clone()
        }
    }

    pub fn save(self: &Example, path: String) {
        let mut file = File::create(path).unwrap();
        rmp_serde::encode::write(&mut file, self).unwrap();
    }

    pub fn load(path: String) -> Example {
        let file = File::open(path).unwrap();
        rmp_serde::decode::from_read(file).unwrap()
    }
}

#[derive(Serialize, Deserialize)]
pub struct Inference {
    pub problem: IRType,
    pub unifications: HashMap<String, HashMap<String, f64>>
}

impl Inference {
    pub fn save(self: &Inference, path: String) {
        let mut file = File::create(path).unwrap();
        rmp_serde::encode::write(&mut file, self).unwrap();
    }

    pub fn load(path: String) -> Inference {
        let file = File::open(path).unwrap();
        rmp_serde::decode::from_read(file).unwrap()
    }
}

// struct Token {
//     name: String
// }

// fn linearize_spine(s: IRSpine, tokens: &mut Vec<Token>) {
    
// }

// fn linearize_term(t: IRTerm, tokens: &mut Vec<Token>) {
    
// }

// fn linearize_type(t: IRType, tokens: &mut Vec<Token>) {
    
// }
