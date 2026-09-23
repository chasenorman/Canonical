use canonical_core::core::{Bind, Position};
use canonical_core::memory::W;

pub struct Tokenization {
    pub tokens: Vec<(Vec<Position>, W<Bind>)>,
    pub goals: Vec<W<Bind>>,
    pub premises: Vec<W<Bind>>
}

impl Tokenization {
    pub fn new() -> Tokenization {
        Tokenization { tokens: Vec::new(), goals: Vec::new(), premises: Vec::new() }
    }
}

// impl Example {
//     pub fn save(self: &Example, path: String) {
//         let mut file = File::create(path).unwrap();
//         rmp_serde::encode::write(&mut file, self).unwrap();
//     }

//     pub fn load(path: String) -> Example {
//         let file = File::open(path).unwrap();
//         rmp_serde::decode::from_read(file).unwrap()
//     }
// }

// struct Token {
//     name: String
// }

// fn linearize_spine(s: IRSpine, tokens: &mut Vec<Token>) {
    
// }

// fn linearize_term(t: IRTerm, tokens: &mut Vec<Token>) {
    
// }

// fn linearize_type(t: IRType, tokens: &mut Vec<Token>) {
    
// }
