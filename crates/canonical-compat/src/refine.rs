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
use std::mem;

/// HTML for the refinement interface.
const HTML: &str = include_str!("../static/index.html");

/// The global state of the backend.
pub static GLOBAL_STATE: OnceLock<Arc<Mutex<AppState>>> = OnceLock::new();

/// When there is no server running, start an Axum server with the given AppState.
pub async fn start_server(state: AppState) {
    let _ = GLOBAL_STATE.set(Arc::new(Mutex::new(state)));

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
        .with_state(GLOBAL_STATE.get().unwrap().clone());

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

pub struct AppState {
    pub current: S<Meta>,
    pub undo: Vec<S<Meta>>,
    pub redo: Vec<S<Meta>>,
    pub autofill: bool,

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

#[derive(Deserialize)]
struct Solve1 {
    meta_id: usize
}

/// Retrieve the HTML file.
async fn index() -> impl IntoResponse {
    Html(HTML)
}

/// Get the current term as HTML, and next metavariable. 
async fn term(State(state): State<Arc<Mutex<AppState>>>) -> Json<serde_json::Value> {
    let state = state.lock().unwrap();
    let meta = state.current.downgrade();
    let mut term = IRTerm::from_term(meta.clone(), &ES::new());
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
        "autofill": state.autofill
    }));
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
    State(state): State<Arc<Mutex<AppState>>>,
    Json(assign): Json<Assign>,
) -> Json<serde_json::Value> {
    let mut state = state.lock().unwrap();

    let index = if assign.def {
        Index::Let(assign.index)
    } else {
        Index::Param(assign.index)
    };
    let mut db = DeBruijnIndex(DeBruijn(assign.debruijn), index);

    let current = state.current.downgrade();
    let (new, map) = try_clone(current.clone()).unwrap();

    let mut meta = map.get(&find_with_id(
        current,
        assign.meta_id,
    )
    .unwrap()).unwrap().clone();

    let mut i = 0;

    while i < 30 {
        let (assn, eqns, _) = test(
            db,
            meta.borrow().gamma.sub_es(db.0).linked.unwrap(),
            meta.clone(),
            false,
        ).unwrap().unwrap();

        meta.borrow_mut().assign(assn, eqns);

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
    let mut state = state.lock().unwrap();
    
    if let Some(prev) = state.undo.pop() {
        let new = mem::replace(&mut state.current, prev);
        state.redo.push(new);
    }
    Json(json!({}))
}

/// Redo an assignment.
async fn redo(State(state): State<Arc<Mutex<AppState>>>) -> Json<serde_json::Value> {
    let mut state = state.lock().unwrap();
    
    if let Some(prev) = state.redo.pop() {
        let new = mem::replace(&mut state.current, prev);
        state.undo.push(new);
    }
    Json(json!({}))
}

/// Reset the prover to a single metavariable.
async fn reset(State(state): State<Arc<Mutex<AppState>>>) -> Json<serde_json::Value> {
    let mut state = state.lock().unwrap(); 
    state.undo = Vec::new();
    state.redo = Vec::new();
    state.current.borrow_mut().assignment = None;
    Json(json!({}))
}

/// Attempt to complete the proof with Canonical.
async fn canonical(State(state): State<Arc<Mutex<AppState>>>) -> Json<serde_json::Value> {
    let mut state = state.lock().unwrap();
    let meta = try_clone(state.current.downgrade()).unwrap().0;
    let prover = Prover { next_root: meta.downgrade(), meta, program_synthesis: false };

    if let Some(term) = canonical_simple(prover) {
        let prev = mem::replace(&mut state.current, term);
        state.redo.clear();
        state.undo.push(prev);
    }
    Json(json!({}))
}

/// Attempt to complete only the specified subtree with Canonical.
async fn canonical1(State(state): State<Arc<Mutex<AppState>>>, Json(solve1) : Json<Solve1>) -> Json<serde_json::Value> {
    let mut state = state.lock().unwrap();
    let current = state.current.downgrade();
    let (meta, map) = try_clone(current.clone()).unwrap();
    let next_root = map.get(&find_with_id(current, solve1.meta_id).unwrap()).unwrap().clone();

    let prover = Prover { next_root, meta, program_synthesis: false };
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

fn find_autofill(meta: W<Meta>) -> Option<(W<Meta>, DeBruijnIndex)> {
    match &meta.borrow().assignment {
        None => {
            let domain: Vec<(DeBruijnIndex, W<Linked>)> = meta.borrow().gamma.iter().filter(|(db, linked)| {
                test(db.clone(), linked.clone(), meta.clone(), false).is_some_and(|o| o.is_some())
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

#[derive(Deserialize)]
struct KV {
    key: String,
    value: bool
}

async fn set(State(state): State<Arc<Mutex<AppState>>>, Json(kv) : Json<KV>) -> Json<serde_json::Value> {
    if kv.key == "autofill" {
        state.lock().unwrap().autofill = kv.value;
    }
    Json(json!({}))
}
