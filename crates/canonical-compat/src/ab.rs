use crate::ai::Example;
use canonical_core::core::*;
use canonical_core::memory::S;
use canonical_core::prover::Prover;
use canonical_core::search::*;
use canonical_core::stats::{LIMIT, STEP_COUNT};
use std::fs;
use std::panic::{self, AssertUnwindSafe};
use std::path::PathBuf;
use std::sync::atomic::Ordering;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// The step limit shared by both runs of each example.
const STEP_LIMIT: u32 = 10_000_000;

/// A/B test `configure(false)` against `configure(true)` on `n` random examples from `Results/`.
/// Pass the same `seed` to rerun on the same set of examples.
pub fn ab_test<F: Fn(bool)>(n: usize, seed: Option<u64>, configure: F) {
    let seed = seed.unwrap_or_else(|| SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos() as u64);
    println!("seed: {seed}");
    watchdog();
    LIMIT.store(STEP_LIMIT, Ordering::Release);

    let files = sample_files("Results", n, seed);
    let mut solved = [0u32; 2];
    let mut log_ratio_sum = 0.0;
    let mut both_solved = 0;

    println!("name, A steps, A solved, B steps, B solved");
    for path in &files {
        let name = path.file_stem().unwrap().to_str().unwrap();
        let results = panic::catch_unwind(AssertUnwindSafe(|| {
            let problem = Example::load(path.to_str().unwrap().to_string()).problem;
            let tb = S::new(problem.to_type(&ES::new(), Polarity::Goal).0);
            let problem_bind = S::new(Bind::new("proof".to_string(), Polarity::Goal));
            let mut owned_linked = Vec::new();
            [false, true].map(|enabled| {
                configure(enabled);
                let prover = Prover::new(tb.downgrade(), problem_bind.downgrade(), &mut owned_linked);
                prover.prove(&|_| RUN.store(false, Ordering::Relaxed), false).0
            })
        }));
        let Ok([a, b]) = results else {
            println!("{name}, error, , , ");
            continue;
        };

        let a_solved = a.solution_count > 0;
        let b_solved = b.solution_count > 0;
        println!("{name}, {}, {}, {}, {}", a.steps, a_solved, b.steps, b_solved);
        solved[0] += a_solved as u32;
        solved[1] += b_solved as u32;
        if a_solved && b_solved {
            both_solved += 1;
            log_ratio_sum += (a.steps.max(1) as f64 / b.steps.max(1) as f64).ln();
        }
    }

    println!("A solved: {}/{}", solved[0], files.len());
    println!("B solved: {}/{}", solved[1], files.len());
    if both_solved > 0 {
        println!("geometric mean speedup (A steps / B steps, over {both_solved} solved by both): {}",
            (log_ratio_sum / both_solved as f64).exp());
    }
}

/// Choose `n` random `.bin` files from `dir`, deterministically given `seed`.
fn sample_files(dir: &str, n: usize, seed: u64) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = fs::read_dir(dir).unwrap()
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|path| path.extension().and_then(|e| e.to_str()) == Some("bin"))
        .collect();
    files.sort();

    let mut state = seed | 1;
    let mut rng = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let n = n.min(files.len());
    for i in 0..n {
        let j = i + rng() as usize % (files.len() - i);
        files.swap(i, j);
    }
    files.truncate(n);
    files
}

/// Cancel the ongoing search if no steps occur for two consecutive seconds.
fn watchdog() {
    std::thread::spawn(|| {
        let mut prev = u32::MAX;
        let mut stalled = 0;
        loop {
            std::thread::sleep(Duration::from_secs(1));
            let count = STEP_COUNT.load(Ordering::Relaxed);
            stalled = if count == prev && RUN.load(Ordering::Relaxed) { stalled + 1 } else { 0 };
            if stalled >= 2 {
                eprintln!("watchdog: search stalled, cancelling");
                RUN.store(false, Ordering::Relaxed);
            }
            prev = count;
        }
    });
}
