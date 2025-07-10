use canonical_core::core::*;
use canonical_core::stats::*;
use canonical_core::prover::Prover;
use canonical_core::memory::S;
use crate::refine::*;
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
#[tokio::main]
pub async fn main() {
    let tb = IRType::load("lean/debug.json".to_string()).to_type(&ES::new());
    let entry = &tb.codomain.borrow().gamma.linked.as_ref().unwrap().borrow().node.entry;
    let node = Node { 
        entry: Entry { params_id: entry.params_id, lets_id: entry.lets_id, subst: None, 
            context: Some(Context(tb.types.downgrade(), tb.codomain.borrow().gamma.clone(), tb.codomain.borrow().bindings.clone()))}, 
        bindings: tb.codomain.borrow().gamma.linked.as_ref().unwrap().borrow().node.bindings.clone() 
    };
    let mut owned_linked = Vec::new();
    let es = ES::new().append(node, &mut owned_linked);
    let tb_ref = S::new(tb);
    let problem_bind = S::new(Bind::new("proof".to_string()));
    let ty = Type(tb_ref.downgrade(), es, problem_bind.downgrade());
    let prover = Prover::new(ty);

    // let state = AppState {
    //     current: prover.meta,
    //     undo: Vec::new(),
    //     redo: Vec::new(),
    //     autofill: true,
    //     constraints: false,
    //     _owned_linked: owned_linked,
    //     _owned_tb: tb_ref,
    //     _owned_bind: problem_bind
    // };

    // start_server(state).await;

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
        let mut owned_linked = Vec::new();
        println!("{}", now.elapsed().unwrap().as_secs_f32());
        println!("{}", IRSpine::from_body::<false>(term.whnf::<false, ()>(&mut owned_linked, &mut ()), false));
        std::process::exit(0);
    }, true);
}