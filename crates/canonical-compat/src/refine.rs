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
use std::mem;

/// HTML for the refinement interface.
const HTML: &str = include_str!("../static/index.html");

/// The maximum number of forced moves that can be made on the user's behalf at one time.
const AUTOFILL_LIMIT: u32 = 30;

/// The global state of the backend.
pub static GLOBAL_STATE: OnceLock<Arc<Mutex<AppState>>> = OnceLock::new();

/// When there is no server running, start an Axum server with the given AppState.
pub async fn start_server(state: AppState) {
    let state = Arc::new(Mutex::new(state));

    let app = Router::new()
        .route("/", get(index))
        .route("/assign", post(assign))
        .route("/undo", post(undo))
        .route("/redo", post(redo))
        .route("/reset", post(reset))
        .route("/term", post(term))
        .route("/canonical", post(canonical))
        .route("/canonical1", post(canonical1))
        .route("/set", post(set))
        .with_state(state.clone());

    let _ = GLOBAL_STATE.set(state);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

/// Internal state for the Axum webserver.
pub struct AppState {
    /// The term currently being displayed.
    pub current: S<Meta>,
    /// The undo stack.
    pub undo: Vec<S<Meta>>,
    /// The redo stack.
    pub redo: Vec<S<Meta>>,
    /// Whether to automatically make forced moves. 
    pub autofill: bool,
    pub constraints: bool,

    // For ownership purposes.
    pub _owned_linked: Vec<S<Linked>>,
    pub _owned_tb: S<TypeBase>,
    pub _owned_bind: S<Bind>
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

/// Data structure sent when Solve1 is pressed.
#[derive(Deserialize)]
struct Solve1 {
    /// Hashcode of the metavariable to be solved.
    meta_id: usize
}

/// Retrieve the HTML file.
async fn index() -> impl IntoResponse {
    Html(HTML)
}

/// Get the current term as HTML, and next metavariable. 
async fn term(State(state): State<Arc<Mutex<AppState>>>) -> Json<serde_json::Value> {
    let Ok(state) = state.lock() else {
        return Json(json!({}))
    };
    let meta = state.current.downgrade();
    let mut owned_linked = Vec::new();
    let mut term = IRTerm::from_body(Term { base: meta.clone(), es: meta.borrow().gamma.clone() }.whnf(&mut owned_linked, &mut ()), true);
    term.params = Vec::new();
    term.lets = Vec::new();
    let html = term.to_string();
    let next = Meta::next(meta)
        .next
        .map(|m| m.meta.borrow() as *const Meta as usize);

    return Json(json!({ 
        "html": html, 
        "next": next, 
        "undo": !state.undo.is_empty(),
        "redo": !state.redo.is_empty(),
        "autofill": state.autofill,
        "constraints": state.constraints
    }));
}

/// Perform the assignment on the prover in the state. 
async fn assign(
    State(state): State<Arc<Mutex<AppState>>>,
    Json(assign): Json<Assign>,
) -> Json<serde_json::Value> {
    let Ok(mut state) = state.lock() else {
        return Json(json!({}))
    };

    let index = if assign.def {
        Index::Let(assign.index)
    } else {
        Index::Param(assign.index)
    };
    let mut db = DeBruijnIndex(DeBruijn(assign.debruijn), index);

    let current = state.current.downgrade();
    let (new, map) = Meta::try_clone(current.clone()).unwrap();

    let mut meta = map.get(&find_with_id(
        current,
        assign.meta_id,
    )
    .unwrap()).unwrap().clone();

    let mut i = 0;

    while i < AUTOFILL_LIMIT {
        let Some(Some((assn, eqns, redexes, _))) = test(
            db,
            meta.borrow().gamma.sub_es(db.0).linked.unwrap(),
            meta.clone()
        ) else { break; };

        meta.borrow_mut().assign(assn, eqns, redexes);

        if !state.autofill {
            break;
        }
        
        if let Some((found, found_db)) = find_autofill(new.downgrade()) {
            meta = found;
            db = found_db;
        } else {
            break;
        }

        i += 1;
    }

    let prev = mem::replace(&mut state.current, new);
    state.redo.clear();
    state.undo.push(prev);

    Json(json!({}))
}

/// Undo an assignment.
async fn undo(State(state): State<Arc<Mutex<AppState>>>) -> Json<serde_json::Value> {
    let Ok(mut state) = state.lock() else {
        return Json(json!({}))
    };
    
    if let Some(prev) = state.undo.pop() {
        let new = mem::replace(&mut state.current, prev);
        state.redo.push(new);
    }
    Json(json!({}))
}

/// Redo an assignment.
async fn redo(State(state): State<Arc<Mutex<AppState>>>) -> Json<serde_json::Value> {
    let Ok(mut state) = state.lock() else {
        return Json(json!({}))
    };
    
    if let Some(prev) = state.redo.pop() {
        let new = mem::replace(&mut state.current, prev);
        state.undo.push(new);
    }
    Json(json!({}))
}

/// Reset the prover to a single metavariable.
async fn reset(State(state): State<Arc<Mutex<AppState>>>) -> Json<serde_json::Value> {
    let Ok(mut state) = state.lock() else {
        return Json(json!({}))
    }; 
    state.undo = Vec::new();
    state.redo = Vec::new();
    state.current.borrow_mut().assignment = None;
    Json(json!({}))
}

/// Attempt to complete the proof with Canonical.
async fn canonical(State(state): State<Arc<Mutex<AppState>>>) -> Json<serde_json::Value> {
    let Ok(mut state) = state.lock() else {
        return Json(json!({}))
    };
    let meta = Meta::try_clone(state.current.downgrade()).unwrap().0;
    let prover = Prover { next_root: meta.downgrade(), meta };

    if let Some(term) = canonical_simple(prover) {
        let prev = mem::replace(&mut state.current, term);
        state.redo.clear();
        state.undo.push(prev);
    }
    Json(json!({}))
}

/// Attempt to complete only the specified subtree with Canonical.
async fn canonical1(State(state): State<Arc<Mutex<AppState>>>, Json(solve1) : Json<Solve1>) -> Json<serde_json::Value> {
    let Ok(mut state) = state.lock() else {
        return Json(json!({}))
    };
    let current = state.current.downgrade();
    let (meta, map) = Meta::try_clone(current.clone()).unwrap();
    let next_root = map.get(&find_with_id(current, solve1.meta_id).unwrap()).unwrap().clone();

    let prover = Prover { next_root, meta };
    if let Some(term) = canonical_simple(prover) {
        let prev = mem::replace(&mut state.current, term);
        state.redo.clear();
        state.undo.push(prev);
    }
    Json(json!({}))
}

/// Run Canonical for 1 second on `prover`, returning the term if one is found.
fn canonical_simple(prover: Prover) -> Option<S<Meta>> {
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        prover.prove(&|value| {
            if let Some(cloned) = Meta::try_clone(value.base) {
                let _ = tx.send(Some(cloned.0));
            } 
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

/// If there exists a metavariable with a single domain element, 
/// return that metavariable and the `DeBruijnIndex` of the variable.
fn find_autofill(meta: W<Meta>) -> Option<(W<Meta>, DeBruijnIndex)> {
    match &meta.borrow().assignment {
        None => {
            let domain: Vec<(DeBruijnIndex, W<Linked>)> = meta.borrow().gamma.iter().filter(|(db, linked)| {
                test(db.clone(), linked.clone(), meta.clone()).is_some_and(|o| o.is_some())
            }).collect();

            if domain.len() == 1 {
                Some((meta, domain[0].0))
            } else {
                None
            }
        }
        Some(assignment) => {
            for arg in assignment.args.iter() {
                if let Some(found) = find_autofill(arg.downgrade()) {
                    return Some(found);
                }
            }
            None
        }
    }
}

/// A key-value pair, for setting options through Axum.
#[derive(Deserialize)]
struct KV {
    key: String,
    value: bool
}

/// Sets the given option flag.
async fn set(State(state): State<Arc<Mutex<AppState>>>, Json(kv) : Json<KV>) -> Json<serde_json::Value> {
    let Ok(mut state) = state.lock() else {
        return Json(json!({}))
    };

    if kv.key == "autofill" {
        state.autofill = kv.value;
    } else if kv.key == "constraints" {
        state.constraints = kv.value;
    }
    Json(json!({}))
}
