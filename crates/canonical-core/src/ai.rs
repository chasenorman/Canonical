//! Fills `WEIGHTS` from a problem's `Tokenization` with a transformer trained in
//! CanonicalHeuristics. Its `scripts/export_onnx.py` writes `model.onnx`, which takes the
//! tokenization's paths and returns the weight matrix; burn-onnx compiles it in, weights
//! included (see `build.rs`). It runs on the GPU when there is one it can use.

use std::iter;
use std::panic;
use std::sync::{Arc, Mutex};
use std::thread;

use burn::tensor::backend::Backend;
use burn::tensor::{DType, Int, Tensor, TensorData};
use burn::{Dispatch, DispatchDevice};
use once_cell::sync::Lazy;

use crate::core::{Decl, Polarity, Position};
use crate::heuristic::WEIGHTS;
use crate::memory::W;

#[derive(Default)]
pub struct Tokenization {
    pub tokens: Vec<(Vec<Position>, W<Decl>)>,
    pub goals: Vec<W<Decl>>,
    pub premises: Vec<W<Decl>>
}

impl Tokenization {
    pub fn new() -> Tokenization {
        Tokenization::default()
    }

    /// Record `decl` as a goal or premise by `polarity`, storing its index in the list on the decl.
    pub fn declare(&mut self, mut decl: W<Decl>, polarity: Polarity) {
        let list = match polarity {
            Polarity::Goal => &mut self.goals,
            Polarity::Premise => &mut self.premises
        };
        decl.borrow_mut().index = list.len();
        list.push(decl);
    }
}

#[allow(dead_code, clippy::all)]
mod model {
    extern crate alloc;
    include!(concat!(env!("OUT_DIR"), "/model/model.rs"));
}

type Model = model::Model<Dispatch>;

/// The model saw at most this many rows (tokens plus binds) in training.
const MAX_ROWS: usize = 5000;

/// A path step as symbols, the matrices the model multiplies by in turn: `Type`, `LHS`, `RHS`
/// are 0, 1, 2, and `Kind(i)` is Kind's "right" i + 1 times, then its "down" (3 and 7 for `Rule`,
/// 4 and 8 `Param`, 5 and 9 `Let`, 6 and 10 `Arg`). `PAD`, the identity, pads paths to one length.
fn step(position: &Position) -> impl Iterator<Item = i64> {
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

/// The model's inputs for `tokens`, or `None` if it has no premises or is too big.
fn inputs(tokens: &Tokenization) -> Option<[TensorData; 4]> {
    let rows = tokens.tokens.len() + tokens.goals.len() + tokens.premises.len();
    if tokens.premises.is_empty() || rows > MAX_ROWS {
        return None;
    }
    let paths: [Vec<&[Position]>; 4] = [
        tokens.tokens.iter().map(|(p, _)| &p[..]).collect(),
        tokens.tokens.iter().map(|(_, b)| &b.borrow().position[..]).collect(),
        tokens.goals.iter().map(|b| &b.borrow().position[..]).collect(),
        tokens.premises.iter().map(|b| &b.borrow().position[..]).collect(),
    ];
    let length = paths.iter().flatten().map(|p| p.iter().flat_map(step).count()).max().unwrap_or(0).max(1);
    Some(paths.map(|paths| {
        let data: Vec<i64> = paths
            .iter()
            .flat_map(|p| p.iter().flat_map(step).chain(iter::repeat(PAD)).take(length))
            .collect();
        TensorData::new(data, [paths.len(), length])
    }))
}

fn run((model, device): &(Model, DispatchDevice), inputs: [TensorData; 4]) -> Vec<Vec<f32>> {
    let [positions, declarations, goals, premises] =
        inputs.map(|d| Tensor::<Dispatch, 2, Int>::from_data(d, (device, DType::I64)));
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

/// `tokens`' goal × premise weights, indexed by `Decl::index`, or `None` if the model
/// doesn't apply.
pub fn weight(tokens: &Tokenization) -> Option<Vec<Vec<f32>>> {
    inputs(tokens).map(|inputs| run(&MODEL.lock().unwrap(), inputs))
}

/// Resets `WEIGHTS` to uniform, then sets it to `weight(tokens)` from a background thread
/// unless another problem has reset it since. Search reads `WEIGHTS` as it goes, so it
/// needn't wait.
pub fn start(tokens: &Tokenization) {
    // A new allocation, so the thread can tell whether `WEIGHTS` is still this problem's.
    let uniform = Arc::new(Vec::new());
    WEIGHTS.store(uniform.clone());
    let Some(inputs) = inputs(tokens) else { return };
    thread::spawn(move || {
        let model = MODEL.lock().unwrap();
        // Problems started in quick succession queue up here: only the latest runs.
        if !Arc::ptr_eq(&WEIGHTS.load(), &uniform) {
            return;
        }
        let weight = run(&model, inputs);
        WEIGHTS.compare_and_swap(&uniform, Arc::new(weight));
    });
}
