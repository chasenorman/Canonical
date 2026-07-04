use canonical_core::core::*;
use canonical_core::stats::*;
use canonical_core::prover::Prover;
pub mod ir;
pub mod refine;
pub mod reduction;
pub mod ai;
use ir::*;
use std::time::SystemTime;

/// Manually construct an IRExpr body.
#[allow(unused_macros)]
macro_rules! t {
    ($s : expr $(, $arg : expr)*) => {
        IRExpr {
            params: vec![],
            lets: vec![],
            spine: IRSpine {
                head: $s.to_string(),
                args: vec![$($arg),*],
                premise_rules: vec![]
            },
            goal_rules: vec![]
        }
    };
}

/// Manually construct a lambda IRExpr.
#[allow(unused_macros)]
macro_rules! l {
    ($params : expr, $s : expr $(, $arg : expr)*) => {
        IRExpr {
            params: $params.iter().map(|name| IRDecl { name: name.to_string(), typ: None, equations: vec![] }).collect(),
            lets: vec![],
            spine: IRSpine {
                head: $s.to_string(),
                args: vec![$($arg),*],
                premise_rules: vec![]
            },
            goal_rules: vec![]
        }
    };
}

/// Manually construct an IRExpr codomain.
#[allow(unused_macros)]
macro_rules! T {
    () => {
        None as Option<IRExpr>
    };
    ($s : expr $(, $arg : expr)*) => {
        Some(t!($s $(, $arg)*))
    };
}

/// Manually construct a Pi IRExpr.
#[allow(unused_macros)]
macro_rules! P {
    ($params : expr, $s : expr $(, $arg : expr)*) => {
        Some(IRExpr {
            params: $params.into_iter().map(|(name, typ)| IRDecl { name: name.to_string(), typ, equations: vec![] }).collect(),
            lets: vec![],
            spine: IRSpine {
                head: $s.to_string(),
                args: vec![$($arg),*],
                premise_rules: vec![]
            },
            goal_rules: vec![]
        })
    };
}

/// Entrypoint for CLI, which reads a problem from a json file. 
/// You can create a json file using the `+debug` tactic option.
#[tokio::main]
pub async fn main() {
    let problem = IRDecl::load("lean/debug.json".to_string());
    let mut owned_linked = Vec::new();

    let decl = problem.to_problem(&mut owned_linked);
    let prover = Prover::new(decl.downgrade());
    // let state = AppState {
    //     current: Meta::try_clone(prover.metas[0].downgrade()).unwrap().0,
    //     undo: Vec::new(),
    //     redo: Vec::new(),
    //     autofill: true,
    //     constraints: false,
    //     _owned_linked: owned_linked,
    //     _owned_bind: decl,
    //     _owned_provers: vec![prover]
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
        println!("{}", IRSpine::from_body::<false>(term.whnf::<false, ()>(&mut owned_linked, &mut (), false), false));
        std::process::exit(0);
    }, true);
}