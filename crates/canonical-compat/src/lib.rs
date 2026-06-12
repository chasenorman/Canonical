use canonical_core::core::*;
use canonical_core::memory::S;
use canonical_core::search::EXPERIMENT;
use std::sync::atomic::Ordering;
pub mod ir;
pub mod refine;
pub mod reduction;
pub mod ai;
pub mod ab;
use ir::*;
use std::time::SystemTime;
use canonical_core::stats::STEP_COUNT;
use canonical_core::prover::Prover;

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

// Entrypoint for CLI: A/B test the `EXPERIMENT` flag on random examples from `Results/`.
// Usage: `canonical-compat [count] [seed]` (defaults: 30 examples, time-based seed).
// #[tokio::main]
// pub async fn main() {
//     let count = std::env::args().nth(1).and_then(|arg| arg.parse().ok()).unwrap_or(30);
//     let seed = std::env::args().nth(2).and_then(|arg| arg.parse().ok());
//     ab::ab_test(count, seed, |enabled| EXPERIMENT.store(enabled, Ordering::Release));
// }

#[tokio::main]
pub async fn main() {
    let irt = IRType::load("lean/debug.json".to_string());
    let tb = S::new(irt.to_type(&ES::new(), Polarity::Goal).0);
    let problem_bind = S::new(Bind::new("proof".to_string(), Polarity::Goal));
    let mut owned_linked = Vec::new();
    
    let prover = Prover::new(tb.downgrade(), problem_bind.downgrade(), &mut owned_linked);
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