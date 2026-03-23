use crate::ir::*;
use serde::{Serialize, Deserialize};
use std::fs::File;

#[derive(Serialize, Deserialize)]
pub struct Example {
    pub problem: IRType,
    pub solution: IRSpine
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