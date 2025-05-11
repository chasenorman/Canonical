use crate::ir::*;
use axum::{
    extract::State,
    response::{Html, IntoResponse},
    routing::{get, post},
    Json, Router,
};
use canonical_core::core::*;
use canonical_core::memory::*;
use canonical_core::prover::Prover;
use canonical_core::search::*;
use serde::Deserialize;
use serde_json::json;
use std::sync::atomic::Ordering;
use std::sync::mpsc;
use std::sync::{Arc, Mutex, OnceLock};
use std::thread;
use std::time::Duration;
use hashbrown::HashMap;
use canonical_core::prover::transfer;

/// HTML for the refinement interface.
const HTML: &str = include_str!("../static/index.html");

/// The global state of the backend.
pub static GLOBAL_STATE: OnceLock<Arc<AppState>> = OnceLock::new();

/// When there is no server running, start an Axum server with the given AppState.
pub async fn start_server(state: AppState) {
    let _ = GLOBAL_STATE.set(Arc::new(state));

    let app = Router::new()
        .route("/", get(index))
        .route("/assign", post(assign))
        .route("/undo", post(undo))
        .route("/reset", post(reset))
        .route("/term", post(term))
        .route("/canonical", post(canonical))
        .route("/canonical1", post(canonical1))
        .with_state(GLOBAL_STATE.get().unwrap().clone());

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

pub struct AppState {
    pub stack: Mutex<Vec<S<Meta>>>,

    // For ownership purposes.
    pub _owned_linked: Mutex<Vec<S<Linked>>>,
    pub _owned_tb: Mutex<S<TypeBase>>,
    pub _owned_bind: Mutex<S<Bind>>
}

/// Sent from JS to represent an assignment.
#[derive(Deserialize, Debug)]
struct Assign {
    /// Hashcode of the metavariable to assign.
    meta_id: usize,
    // DeBruijnIndex
    debruijn: u32,
    index: usize,
    def: bool
}

#[derive(Deserialize)]
struct Solve1 {
    meta_id: usize
}

/// Retrieve the HTML file.
async fn index() -> impl IntoResponse {
    Html(HTML)
}

/// Get the current term as HTML, and next metavariable. 
async fn term(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    let meta = state.stack.lock().unwrap().last().unwrap().downgrade();
    let mut term = IRTerm::from_term(meta.clone(), &ES::new());
    term.params = Vec::new();
    term.lets = Vec::new();
    let html = term.to_string();
    let next = Meta::next(meta)
        .next
        .map(|m| m.meta.borrow() as *const Meta as usize);

    return Json(json!({ "html": html, "next": next }));
}

pub fn try_clone(meta: W<Meta>) -> Option<(S<Meta>, HashMap<W<Meta>, W<Meta>>)> {
    let new = S::new(Meta::new(meta.borrow().typ.as_ref().unwrap().clone()));
    let mut map = HashMap::new();
    if transfer(meta, new.downgrade(), &mut map) {
        return Some((new, map))
    }
    return None
}

/// Perform the assignment on the prover in the state. 
async fn assign(
    State(state): State<Arc<AppState>>,
    Json(assign): Json<Assign>,
) -> Json<serde_json::Value> {
    let index = if assign.def {
        Index::Let(assign.index)
    } else {
        Index::Param(assign.index)
    };
    let db = DeBruijnIndex(DeBruijn(assign.debruijn), index);

    let current = state.stack.lock().unwrap().last().unwrap().downgrade();
    let (new, map) = try_clone(current.clone()).unwrap();

    let mut meta = map.get(&find_with_id(
        current,
        assign.meta_id,
    )
    .unwrap()).unwrap().clone();

    let (assn, eqns, _) = test(
        db,
        meta.borrow().gamma.sub_es(db.0).linked.unwrap(),
        meta.clone(),
        false,
    )
    .unwrap()
    .unwrap();

    meta.borrow_mut().assign(assn, eqns);
    state.stack.lock().unwrap().push(new);
    Json(json!({}))
}

/// Undo an assignment.
async fn undo(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    let mut stack = state.stack.lock().unwrap();
    if stack.len() > 1 {
        stack.pop();
    }
    Json(json!({}))
}

/// Reset the prover to a single metavariable.
async fn reset(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    state.stack.lock().unwrap().truncate(1);
    Json(json!({}))
}

/// Attempt to complete the proof with Canonical.
async fn canonical(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    let meta = try_clone(state.stack.lock().unwrap().last().unwrap().downgrade()).unwrap().0;
    let prover = Prover { next_root: meta.downgrade(), meta, program_synthesis: false };
    let term = canonical_simple(prover);
    let html = term.map(|term| {
        let mut ir_term = IRTerm::from_term(term.downgrade(), &ES::new());
        state.stack.lock().unwrap().push(term);
        ir_term.params = Vec::new();
        ir_term.lets = Vec::new();
        ir_term.to_string()
    });
    Json(json!({ "html": html }))
}

/// Attempt to complete only the specified subtree with Canonical.
async fn canonical1(State(state): State<Arc<AppState>>, Json(solve1) : Json<Solve1>) -> Json<serde_json::Value> {
    let current = state.stack.lock().unwrap().last().unwrap().downgrade();
    let (meta, map) = try_clone(current.clone()).unwrap();
    let next_root = map.get(&find_with_id(current, solve1.meta_id).unwrap()).unwrap().clone();

    let prover = Prover { next_root, meta, program_synthesis: false };
    let term = canonical_simple(prover);
    let html = term.map(|term| {
        let mut ir_term = IRTerm::from_term(term.downgrade(), &ES::new());
        state.stack.lock().unwrap().push(term);
        ir_term.params = Vec::new();
        ir_term.lets = Vec::new();
        ir_term.to_string()
    });
    Json(json!({ "html": html }))
}

/// Run Canonical for 1 second on `prover`, returning the term if one is found.
fn canonical_simple(prover: Prover) -> Option<S<Meta>> {
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        prover.prove(&|value| {
            let _ = tx.send(Some(try_clone(value.base).unwrap().0));
        }, false);
        tx.send(None)
    });

    let term = rx.recv_timeout(Duration::from_secs(1));
    RUN.store(false, Ordering::Relaxed);
    term.ok().flatten()
}

/// Find a metavariable with the given hashcode in the children of `meta`.
fn find_with_id(meta: W<Meta>, id: usize) -> Option<W<Meta>> {
    match &meta.borrow().assignment {
        None => {
            if (meta.borrow() as *const Meta as usize) == id {
                Some(meta)
            } else {
                None
            }
        }
        Some(assignment) => {
            for arg in assignment.args.iter() {
                if let Some(found) = find_with_id(arg.downgrade(), id) {
                    return Some(found);
                }
            }
            None
        }
    }
}
