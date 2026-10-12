//! Fills `WEIGHTS` from a problem's `Tokenization` with a transformer trained in
//! CanonicalHeuristics. Its `scripts/export_onnx.py` writes `model.onnx`, which takes the
//! tokenization's paths and returns the weight matrix; burn-onnx compiles it in, weights
//! included (see `build.rs`). It runs on the GPU when there is one it can use.

use std::iter;
use std::panic;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use burn::tensor::backend::Backend;
use burn::tensor::{DType, Int, Tensor, TensorData};
use burn::{Dispatch, DispatchDevice};
use once_cell::sync::Lazy;

use crate::core::{Decl, Position};
use crate::heuristic::WEIGHTS;
use crate::memory::W;

#[derive(Default)]
pub struct Tokenization {
    pub tokens: Vec<(Vec<Position>, W<Decl>)>,
    pub goals: Vec<W<Decl>>,
    pub premises: Vec<W<Decl>>
}

#[allow(dead_code, clippy::all)]
mod model {
    extern crate alloc;
    include!(concat!(env!("OUT_DIR"), "/model/model.rs"));
}

type Model = model::Model<Dispatch>;

/// The model saw at most this many rows (tokens plus binds) in training.
const MAX_ROWS: usize = 5000;

/// `path` as symbols, the matrices the model multiplies by in turn: `Type`, `LHS`, `RHS` are 0,
/// 1, 2, and `Kind(i)` is Kind's "right" i + 1 times, then its "down" (3 and 7 for `Rule`, 4 and 8
/// `Param`, 5 and 9 `Let`, 6 and 10 `Arg`). `PAD`, the identity, pads paths to one length.
fn symbols(path: &[Position]) -> Vec<i64> {
    path.iter().flat_map(|position| {
        let (right, repeats, last) = match *position {
            Position::Type => (0, 0, 0),
            Position::LHS => (0, 0, 1),
            Position::RHS => (0, 0, 2),
            Position::Rule(i) => (3, i + 1, 7),
            Position::Param(i) => (4, i + 1, 8),
            Position::Let(i) => (5, i + 1, 9),
            Position::Arg(i) => (6, i + 1, 10),
        };
        iter::repeat_n(right, repeats).chain([last])
    }).collect()
}

const PAD: i64 = 11;

/// The model, on wgpu's GPU (Metal, Vulkan or DX12), loaded when first needed. The lock
/// also keeps problems from running at once.
static MODEL: Lazy<Mutex<(Model, DispatchDevice)>> = Lazy::new(|| {
    let on = |device: DispatchDevice| (Model::from_embedded(&device), device);
    // Burn panics when wgpu has no adapter at all, not even a software one: use the CPU.
    let model = panic::catch_unwind(|| on(DispatchDevice::default()))
        .unwrap_or_else(|_| on(DispatchDevice::NdArray(Default::default())));
    Mutex::new(model)
});

pub struct Symbols {
    pub token_positions: TensorData,
    pub token_declarations: TensorData,
    pub goals: TensorData,
    pub premises: TensorData
}

impl Symbols {
    pub fn new(tokens: &Tokenization) -> Symbols {
        let declaration = |d: &W<Decl>| symbols(&d.borrow().position);
        let paths: [Vec<Vec<i64>>; 4] = [
            tokens.tokens.iter().map(|(p, _)| symbols(p)).collect(),
            tokens.tokens.iter().map(|(_, d)| declaration(d)).collect(),
            tokens.goals.iter().map(declaration).collect(),
            tokens.premises.iter().map(declaration).collect(),
        ];
        let length = paths.iter().flatten().map(Vec::len).max().unwrap_or(0);
        let [token_positions, token_declarations, goals, premises] = paths.map(|paths| {
            let shape = [paths.len(), length];
            TensorData::new(paths.into_iter().flat_map(|mut p| { p.resize(length, PAD); p }).collect(), shape)
        });
        Symbols { token_positions, token_declarations, goals, premises }
    }

    /// The model's inputs, on `device`.
    fn inputs(self, device: &DispatchDevice) -> [Tensor<Dispatch, 2, Int>; 4] {
        [self.token_positions, self.token_declarations, self.goals, self.premises]
            .map(|d| Tensor::from_data(d, (device, DType::I64)))
    }
}

fn run((model, device): &(Model, DispatchDevice), symbols: Symbols) -> Vec<Vec<f32>> {
    let [positions, declarations, goals, premises] = symbols.inputs(device);
    let weight = model.forward(positions, declarations, goals, premises);
    let [_, n] = weight.dims();
    let weight = weight.into_data().to_vec::<f32>().unwrap();
    // CubeCL keeps the memory it allocates, so without this the GPU fills up over a few dozen
    // problems and inference then fails. `Dispatch` doesn't forward `memory_cleanup`.
    if let DispatchDevice::Wgpu(device) = device {
        <burn::backend::Wgpu as Backend>::memory_cleanup(device);
    }
    let _ = Dispatch::sync(device);
    weight.chunks(n).map(<[f32]>::to_vec).collect()
}

const DELAY: Duration = Duration::from_secs(1);

pub fn start(tokens: &Tokenization) {
    let started = Instant::now();
    let uniform = WEIGHTS.load_full();
    if tokens.premises.is_empty() || tokens.tokens.len() > MAX_ROWS { return; }
    let symbols = Symbols::new(tokens);
    thread::spawn(move || {
        let model = MODEL.lock().unwrap();
        // Problems started in quick succession queue up here: only the latest runs.
        if !Arc::ptr_eq(&WEIGHTS.load(), &uniform) { return; }
        let weight = run(&model, symbols);
        drop(model);
        thread::sleep(DELAY.saturating_sub(started.elapsed()));
        WEIGHTS.compare_and_swap(&uniform, Arc::new(weight));
    });
}
