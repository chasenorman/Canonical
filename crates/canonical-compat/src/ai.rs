use std::collections::HashMap;
use std::fs::File;
use crate::ir::*;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub enum Position {
    Type,
    Rule(usize),
    LHS,
    RHS,
    Param(usize),
    Let(usize),
    Arg(usize),
}

#[derive(Serialize, Deserialize)]
pub struct Token {
    pub position: Vec<Position>,
    pub declaration: Vec<Position>,
}

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
    pub fn save(self: &Example, path: String) {
        let mut file = File::create(path).unwrap();
        rmp_serde::encode::write(&mut file, self).unwrap();
    }

    pub fn load(path: String) -> Example {
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
