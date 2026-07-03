use std::collections::HashMap;
use std::fs::File;
use crate::ir::*;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct Example {
    pub problem: IRDecl,
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

// struct Token {
//     name: String
// }

// fn linearize_spine(s: IRSpine, tokens: &mut Vec<Token>) {
    
// }

// fn linearize_expr(t: IRExpr, tokens: &mut Vec<Token>) {

// }
