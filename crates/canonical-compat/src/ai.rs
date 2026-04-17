use std::collections::HashMap;
use std::fs::File;
use crate::ir::*;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct Example {
    pub problem: IRType,
    pub unifications: HashMap<String, HashMap<String, u32>>
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
