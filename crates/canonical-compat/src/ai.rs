use canonical_core::core::{Decl, Position, Polarity};
use canonical_core::memory::W;

pub struct Tokenization {
    pub tokens: Vec<(Vec<Position>, W<Decl>)>,
    pub goals: Vec<W<Decl>>,
    pub premises: Vec<W<Decl>>
}

impl Tokenization {
    pub fn new() -> Tokenization {
        Tokenization { tokens: Vec::new(), goals: Vec::new(), premises: Vec::new() }
    }

    /// Record `bind` as a goal or premise by `polarity`, storing its index in the list on the bind.
    pub fn declare(&mut self, mut bind: W<Decl>, polarity: Polarity) {
        let list = match polarity {
            Polarity::Goal => &mut self.goals,
            Polarity::Premise => &mut self.premises
        };
        bind.borrow_mut().index = list.len();
        list.push(bind);
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

// fn linearize_expr(t: IRExpr, tokens: &mut Vec<Token>) {

// }
