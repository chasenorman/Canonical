use canonical_core::core::*;
use canonical_core::stats::*;
use canonical_core::prover::Prover;
use canonical_core::memory::{W, S};
pub mod ir;
pub mod refine;
pub mod reduction;
pub mod ai;
use ir::*;
use std::time::SystemTime;
use std::fs;
use canonical_core::search::RUN;
use std::sync::atomic::Ordering;
use std::sync::atomic::AtomicU32;
use std::panic;
use canonical_core::search::DFSResult;

use crate::ai::*;

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

fn size(meta: W<Meta>) -> u32 {
    1 + meta.borrow().assignment.as_ref().unwrap().args.iter().map(|x| size(x.downgrade())).sum::<u32>()
}

fn sanitize(s: String) -> String {
    let mut out = String::new();
    let mut prev_was_underscore = false;

    for c in s.chars() {
        let is_valid = c.is_ascii_alphanumeric();

        if is_valid {
            out.push(c);
            prev_was_underscore = false;
        } else {
            if !prev_was_underscore {
                out.push('_');
                prev_was_underscore = true;
            }
        }
    }

    out
}

pub static LIMIT: AtomicU32 = AtomicU32::new(10000000);

pub fn compare(inference: Inference, prefix: String) -> (DFSResult, DFSResult) {
    let irt = inference.problem;
    let tb = S::new(irt.to_type(&ES::new()));
    let problem_bind = S::new(Bind::new(prefix));
    let mut owned_linked = Vec::new();
    LIMIT.store(10000000, Ordering::Release);
    let prover = Prover::new(tb.downgrade(), problem_bind.downgrade(), &mut owned_linked, None);
    let result0 = prover.prove(&|term: Term| {
        // let mut owned_linked = Vec::new();
        // println!("{}", now.elapsed().unwrap().as_secs_f32());
        // println!("{}", IRSpine::from_body::<false>(term.whnf::<false, ()>(&mut owned_linked, &mut ()), false));
        RUN.store(false, Ordering::Relaxed);
    }, false);
    
    LIMIT.store(result0.0.steps * 10, Ordering::Release);
    let prover = Prover::new(tb.downgrade(), problem_bind.downgrade(), &mut owned_linked, Some(inference.unifications));
    let result = prover.prove(&|term: Term| {
        print!("(found: {})", size(term.base));
        // let mut owned_linked = Vec::new();
        // println!("{}", now.elapsed().unwrap().as_secs_f32());
        // println!("{}", IRSpine::from_body::<false>(term.whnf::<false, ()>(&mut owned_linked, &mut ()), false));
        RUN.store(false, Ordering::Relaxed);
    }, false);
    return (result0.0, result.0)
}

/// Entrypoint for CLI, which reads a problem from a json file. 
/// You can create a json file using the `+debug` tactic option.
#[tokio::main]
pub async fn main() {
    // let mut count = 0;
    // let mut speedup = 0.0;
    std::thread::spawn(move || {
        let mut prev = u32::MAX;
        loop {
            std::thread::sleep(std::time::Duration::from_secs(1));
            let count = STEP_COUNT.load(Ordering::Relaxed);
            let limit = LIMIT.load(Ordering::Relaxed);
            if prev == count || count > limit {
                print!("cancel");
                RUN.store(false, Ordering::Relaxed)
            }
            prev = count;
        }
    });

    for entry in fs::read_dir("canonical_predictions").unwrap().skip(2777) {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) == Some("bin") {
            print!("{}, ", path.to_str().unwrap().to_string());
            // let irt = IRType::load("lean/debug.json".to_string());
            let inference = Inference::load(path.to_str().unwrap().to_string());
            
            let mut prefix = path.file_stem().unwrap().to_str().unwrap().to_string();
            for (i, _) in inference.unifications.iter() {
                if sanitize(i.to_string()) == sanitize(prefix.to_string()) {
                    prefix = i.to_string();
                }
            }

            match panic::catch_unwind(|| compare(inference, prefix)) {
                Ok((result0, result)) => println!(", {}, {}" /*, {} (geom. mean: {})*/, result0.steps, result.steps, /* result0.0.steps as f32 / result.0.steps as f32 , (speedup / count as f32).exp()*/),
                Err(_) => println!("error, ,")
            }
            
            
            // speedup += (result0.0.steps as f32 / result.0.steps as f32).ln();
            // count += 1;
            
        }
    }
}