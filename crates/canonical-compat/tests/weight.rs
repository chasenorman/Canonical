//! `tests/problem.json` and `tests/weight.json` are written by CanonicalHeuristics'
//! `scripts/export_onnx.py`: a problem, and the checkpoint's own weights for it keyed by
//! the goals' and premises' declarations.

use std::collections::HashMap;
use std::thread;
use std::time::{Duration, Instant};

use canonical_compat::ir::IRDecl;
use canonical_core::heuristic::WEIGHTS;
use serde_json::Value;

const DIR: &str = env!("CARGO_MANIFEST_DIR");

#[test]
fn matches_checkpoint() {
    let (_decl, tokens) = IRDecl::load(format!("{DIR}/tests/problem.json")).to_problem();
    let weight = canonical_core::ai::weight(&tokens).unwrap();

    let expected: Value =
        serde_json::from_str(&std::fs::read_to_string(format!("{DIR}/tests/weight.json")).unwrap())
            .unwrap();
    let index = |key: &str| -> HashMap<&str, usize> {
        let keys = expected[key].as_array().unwrap();
        keys.iter().enumerate().map(|(i, k)| (k.as_str().unwrap(), i)).collect()
    };
    let (goals, premises) = (index("goals"), index("premises"));
    assert_eq!((goals.len(), premises.len()), (tokens.goals.len(), tokens.premises.len()));

    for g in &tokens.goals {
        for p in &tokens.premises {
            let row = goals[format!("{:?}", g.borrow().position).as_str()];
            let column = premises[format!("{:?}", p.borrow().position).as_str()];
            let want = expected["weight"][row][column].as_f64().unwrap();
            let got = weight[g.borrow().index][p.borrow().index] as f64;
            assert!((got - want).abs() < 1e-4, "{:?} ← {:?}: {got} vs {want}", g.borrow().name, p.borrow().name);
        }
    }
}

/// `to_problem` starts the heuristic, which fills `WEIGHTS` in the background.
#[test]
fn start_sets_weight() {
    let (_decl, tokens) = IRDecl::load(format!("{DIR}/tests/problem.json")).to_problem();
    let want = canonical_core::ai::weight(&tokens).unwrap();

    let deadline = Instant::now() + Duration::from_secs(60);
    while WEIGHTS.load().is_empty() {
        assert!(Instant::now() < deadline, "start never set WEIGHTS");
        thread::sleep(Duration::from_millis(10));
    }
    let got = WEIGHTS.load();
    assert_eq!(got.len(), want.len());
    for (got, want) in got.iter().zip(&want) {
        assert!(got.iter().zip(want).all(|(a, b)| (a - b).abs() < 1e-6));
    }
}
