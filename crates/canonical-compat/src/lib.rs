use canonical_core::core::*;
use canonical_core::stats::*;
use canonical_core::prover::Prover;
use canonical_core::memory::S;
pub mod ir;
pub mod refine;
pub mod reduction;
use ir::*;
use std::time::SystemTime;

/// Manually construct a IRTerm body.
#[allow(unused_macros)]
macro_rules! t {
    ($s : expr) => {
        IRTerm {
            params: vec![],
            lets: vec![],
            head: $s.to_string(),
            args: vec![]
        }
    };
    ($s : expr, $($arg:expr ),*) => {
        {let mut args = Vec::new();
        $(
            args.push($arg);
        )*
        IRTerm {
            params: vec![],
            lets: vec![],
            head: $s.to_string(),
            args
        }}
    };
}

/// Manually construct a lambda IRTerm.
#[allow(unused_macros)]
macro_rules! l {
    ($params : expr, $s : expr) => {
        IRTerm {
            params: $params.iter().map(|name| IRVar { name: name.to_string(), irrelevant: false }).collect(),
            lets: vec![],
            head: $s.to_string(),
            args: vec![]
        }
    };
    ($params : expr, $s : expr, $( $arg:expr ),*) => {
        {let mut args = Vec::new();
        $(
            args.push($arg);
        )*
        IRTerm {
            params: $params.iter().map(|name| IRVar { name: name.to_string(), irrelevant: false }).collect(),
            lets: vec![],
            head: $s.to_string(),
            args
        }}
    };
}

/// Manually construct a IRType codomain.
#[allow(unused_macros)]
macro_rules! T {
    () => {
        None as Option<IRType>
    };
    ($s : expr) => {
        Some(IRType {
            params: vec![],
            lets: vec![],
            codomain: IRTerm {
                params: vec![],
                lets: vec![],
                head: $s.to_string(),
                args: vec![]
            }
        })
    };
    ($s : expr, $( $arg:expr ),*) => {
        {let mut args = Vec::new();
        $(
            args.push($arg);
        )*
        Some(IRType {
            params: vec![],
            lets: vec![],
            codomain: IRTerm {
                params: vec![],
                lets: vec![],
                head: $s.to_string(),
                args
            }
        })}
    };
}

/// Manually construct a Pi IRType.
#[allow(unused_macros)]
macro_rules! P {
    ($params : expr, $s : expr) => {
        Some(IRType {
            params: $params.into_iter().map(|(_, typ)| typ).collect(),
            lets: vec![],
            codomain: IRTerm {
                params: $params.iter().map(|(name, _)| IRVar { name: name.to_string(), irrelevant: false }).collect(),
                lets: vec![],
                head: $s.to_string(),
                args: vec![]
            }
        })
    };
    ($params : expr, $s : expr, $( $arg:expr ),*) => {
        {let mut args = Vec::new();
        $(
            args.push($arg);
        )*
        Some(IRType {
            params: $params.into_iter().map(|(_, typ)| typ).collect(),
            lets: vec![],
            codomain: IRTerm {
                params: $params.iter().map(|(name, _)| IRVar { name: name.to_string(), irrelevant: false }).collect(),
                lets: vec![],
                head: $s.to_string(),
                args
            }
        })}
    };
}

/// Entrypoint for CLI, which reads a problem from a json file. 
/// You can create a json file using the `+debug` tactic option.
pub fn main() {
    /* let tb = IRType::load("lean/debug.json".to_string()).to_type(&ES::new());
    let entry = &tb.codomain.borrow().gamma.linked.as_ref().unwrap().borrow().node.entry;
    let node = Node { 
        entry: Entry { params_id: entry.params_id, lets_id: entry.lets_id, subst: None, 
            context: Some(Context(tb.types.downgrade(), tb.codomain.borrow().gamma.clone(), tb.codomain.borrow().bindings.clone()))}, 
        bindings: tb.codomain.borrow().gamma.linked.as_ref().unwrap().borrow().node.bindings.clone() 
    };
    let mut owned_linked = Vec::new();
    let es = ES::new().append(node, &mut owned_linked);
    let tb_ref = S::new(tb);
    let problem_bind = S::new(Bind { name: "proof".to_string(), irrelevant: false, rules: Vec::new(), value: Value::Opaque, major: false });
    let ty = Type(tb_ref.downgrade(), es, problem_bind.downgrade());
    let prover = Prover::new(ty, false);

    // Print step count each second.
    std::thread::spawn(move || {
        let mut prev = 0;
        loop {
            std::thread::sleep(std::time::Duration::from_secs(1));
            let count = STEP_COUNT.load(std::sync::atomic::Ordering::Relaxed);
            println!("total: {}", count);
            println!("t/s: {}", count - prev);
            prev = count;
        }
    });
    
    let now = SystemTime::now();
    prover.prove(&|term: Term| {
        println!("{}", now.elapsed().unwrap().as_secs_f32());
        println!("{}", IRTerm::from_term(term.base, &ES::new()));
        std::process::exit(0);
    }, true); */

    // let test = P!([("A", T!()), ("B", T!()), ("f", P!([("x", T!("A"))], "B")), ("a", T!("A"))], "B");
    // let test = P!([("Type", T!()), ("A", T!("Type")), ("B", T!("Type")), ("f", P!([("X", T!("Type")), ("x", T!("X"))], "A")), ("b", T!("B"))], "A");
    
    let add_zero_lhs = t!("+", t!("x"), t!("0"));
    let add_zero_rhs = t!("x");

    let add_succ_lhs = t!("+", t!("x"), t!("S", t!("y")));
    let add_succ_rhs = t!("S", t!("+", t!("x"), t!("y")));

    let zero_add_lhs = t!("+", t!("0"), t!("x"));
    let zero_add_rhs = t!("x");

    let succ_add_lhs = t!("+", t!("S", t!("x")), t!("y"));
    let succ_add_rhs = t!("S", t!("+", t!("x"), t!("y")));

    let add_assoc_lhs = t!("+", t!("x"), t!("+", t!("y"), t!("z")));
    let add_assoc_rhs = t!("+", t!("+", t!("x"), t!("y")), t!("z"));

    let ir_term = IRTerm {
        params: vec![
            IRVar { name: "a".to_string(), irrelevant: false },
            IRVar { name: "b".to_string(), irrelevant: false },
            IRVar { name: "c".to_string(), irrelevant: false }
        ],
        lets: vec![
            IRLet { var: IRVar { name: "0".to_string(), irrelevant: false }, rules: vec![], value: IRValue::Opaque },
            IRLet { var: IRVar { name: "S".to_string(), irrelevant: false }, rules: vec![], value: IRValue::Opaque },
            IRLet { var: IRVar { name: "+".to_string(), irrelevant: false }, rules: vec!
                [
                    IRRule { lhs: add_zero_lhs, rhs: add_zero_rhs }, 
                    IRRule { lhs: add_succ_lhs, rhs: add_succ_rhs },
                    IRRule { lhs: zero_add_lhs, rhs: zero_add_rhs },
                    IRRule { lhs: succ_add_lhs, rhs: succ_add_rhs },
                    IRRule { lhs: add_assoc_lhs, rhs: add_assoc_rhs }
                ], 
                value: IRValue::Opaque }
            ],
        head: "+".to_string(),
        args: vec![t!("a"), t!("S", t!("b"))]
    };
    
    let term = S::new(ir_term.to_term(&ES::new()));
    let rules = &term.borrow().bindings.borrow().lets[2].borrow().rules;

    println!("{}", Term { es: term.borrow().gamma.clone(), base: term.downgrade()}.reduce(rules, &mut Vec::new()).is_some() );
}