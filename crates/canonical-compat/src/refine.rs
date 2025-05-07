use axum::{
    extract::State,
    http::StatusCode,
    response::{Html, IntoResponse},
    routing::{get, post},
    Router, Json,
};
use serde::Deserialize;
use std::{fs, iter::Once, sync::{Arc, Mutex}};
use serde_json::json;
use canonical_core::prover::Prover;
use canonical_core::core::*;
use canonical_core::memory::*;
use canonical_core::search::*;
use crate::ir::*;
use std::thread;
use std::time::{Duration, Instant};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::OnceLock;

const HTML: &str = include_str!("../static/index.html");
pub static GLOBAL_STATE: OnceLock<Arc<AppState>> = OnceLock::new();

pub async fn start_server(state: AppState) {
    GLOBAL_STATE.set(Arc::new(state));

    let app = Router::new()
        .route("/", get(index))
        .route("/assign", post(assign))
        .route("/unassign", post(unassign))
        .route("/reset", post(reset))
        .route("/term", post(term))
        .route("/canonical", post(canonical))
        .with_state(GLOBAL_STATE.get().unwrap().clone());

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

pub struct AppState {
    pub prover: Mutex<Prover>,
    pub assigned: Mutex<Vec<W<Meta>>>,
    pub _owned_linked: Mutex<Vec<S<Linked>>>,
    pub _owned_tb: Mutex<S<TypeBase>>,
    pub _owned_bind: Mutex<S<Bind>>
}

#[derive(Deserialize, Debug)]
struct Assign {
    meta_id: usize,
    debruijn: u32,
    index: usize,
    def: bool
}

async fn index() -> impl IntoResponse {
    Html(HTML)
}

async fn term(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    let mut term = IRTerm::from_term(state.prover.lock().unwrap().meta.downgrade(), &ES::new());
    term.params = Vec::new();
    term.lets = Vec::new();
    let html = term.to_string();
    let next = Meta::next(state.prover.lock().unwrap().meta.downgrade())
        .next.map(|m| m.meta.borrow() as *const Meta as usize);
    
    return Json(json!({ "html": html, "next": next }));
}

async fn assign(State(state): State<Arc<AppState>>, Json(assign): Json<Assign>) -> Json<serde_json::Value> {
    let index = if assign.def {
        Index::Let(assign.index)
    } else {
        Index::Param(assign.index)
    };
    let db = DeBruijnIndex(DeBruijn(assign.debruijn), index);
    let mut meta = find_with_id(state.prover.lock().unwrap().meta.downgrade(), assign.meta_id).unwrap();

    let (assn, eqns, _) = test(db, meta.borrow().gamma.sub_es(db.0).linked.unwrap(), meta.clone(), false).unwrap().unwrap();

    meta.borrow_mut().assign(assn, eqns);
    state.assigned.lock().unwrap().push(meta.clone());
    Json(json!({ }))
}

async fn unassign(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    let mut assigned = state.assigned.lock().unwrap();
    if let Some(mut meta) = assigned.pop() {
        meta.borrow_mut().unassign();
    }
    Json(json!({ }))
}

async fn reset(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    let mut assigned = state.assigned.lock().unwrap();
    assigned.clear();
    let mut prover = state.prover.lock().unwrap();
    prover.meta.borrow_mut().assignment = None; // destroys all metavariables and their equations. 
    Json(json!({ }))
}

async fn canonical(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    let mut prover = state.prover.lock().unwrap();
    let term = canonical_simple(prover.try_clone(prover.meta.downgrade()).unwrap().0);
    if let Some(mut term) = term {
        term.params = Vec::new();
        term.lets = Vec::new();
        Json(json!({ "html": term.to_string() }))
    } else {
        let html : Option<String> = None;
        Json(json!({ "html": html }))
    }
}

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