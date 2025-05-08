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
        .with_state(GLOBAL_STATE.get().unwrap().clone());

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

pub struct AppState {
    /// The prover whose term is being displayed. 
    pub prover: Mutex<Prover>,
    /// The stack of assigned metavariables, for undo.
    pub assigned: Mutex<Vec<W<Meta>>>,

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

/// Retrieve the HTML file.
async fn index() -> impl IntoResponse {
    Html(HTML)
}

/// Get the current term as HTML, and next metavariable. 
async fn term(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    let mut term = IRTerm::from_term(state.prover.lock().unwrap().meta.downgrade(), &ES::new());
    term.params = Vec::new();
    term.lets = Vec::new();
    let html = term.to_string();
    let next = Meta::next(state.prover.lock().unwrap().meta.downgrade())
        .next
        .map(|m| m.meta.borrow() as *const Meta as usize);

    return Json(json!({ "html": html, "next": next }));
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
    let mut meta = find_with_id(
        state.prover.lock().unwrap().meta.downgrade(),
        assign.meta_id,
    )
    .unwrap();

    let (assn, eqns, _) = test(
        db,
        meta.borrow().gamma.sub_es(db.0).linked.unwrap(),
        meta.clone(),
        false,
    )
    .unwrap()
    .unwrap();

    meta.borrow_mut().assign(assn, eqns);
    state.assigned.lock().unwrap().push(meta.clone());
    Json(json!({}))
}

/// Undo an assignment.
async fn undo(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    let mut assigned = state.assigned.lock().unwrap();
    if let Some(mut meta) = assigned.pop() {
        meta.borrow_mut().unassign();
    }
    Json(json!({}))
}

/// Reset the prover to a single metavariable.
async fn reset(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    let mut assigned = state.assigned.lock().unwrap();
    assigned.clear();
    let mut prover = state.prover.lock().unwrap();
    prover.meta.borrow_mut().assignment = None; // destroys all metavariables and their equations.
    Json(json!({}))
}

/// Attempt to complete the proof with Canonical.
async fn canonical(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    let prover = state.prover.lock().unwrap();
    let term = canonical_simple(prover.try_clone(prover.meta.downgrade()).unwrap().0);
    let html = term.map(|mut term| {
        term.params = Vec::new();
        term.lets = Vec::new();
        term.to_string()
    });
    Json(json!({ "html": html }))
}

/// Run Canonical for 1 second on `prover`, returning the term if one is found.
fn canonical_simple(prover: Prover) -> Option<IRTerm> {
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        prover.prove(&|value| {
            let _ = tx.send(Some(IRTerm::from_term(value.base, &ES::new())));
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
