use axum::{
    extract::State,
    http::StatusCode,
    response::{Html, IntoResponse},
    routing::{get, post},
    Router, Json,
};
use serde::Deserialize;
use std::{fs, sync::{Arc, Mutex}};
use serde_json::json;
use canonical_core::prover::Prover;
use canonical_core::core::*;
use canonical_core::memory::*;
use canonical_core::search::*;
use crate::ir::*;

pub async fn main(prover: Prover) {
    let state = AppState { prover: Mutex::new(prover) };
    let app = Router::new()
        .route("/", get(index))
        .route("/assign", post(assign))
        .route("/unassign", post(unassign))
        .route("/term", post(term))
        .with_state(Arc::new(state));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

struct AppState {
    prover: Mutex<Prover>
}

#[derive(Deserialize, Debug)]
struct Assign {
    meta_id: usize,
    debruijn: u32,
    index: usize,
    def: bool
}

async fn index() -> impl IntoResponse {
    match fs::read_to_string("crates/canonical-compat/static/index.html") {
        Ok(contents) => Html(contents).into_response(),
        Err(_) => (StatusCode::INTERNAL_SERVER_ERROR, "Failed to load index.html").into_response(),
    }
}

async fn term(State(state): State<Arc<AppState>>) -> Html<std::string::String> {
    Html(IRTerm::from_term(state.prover.lock().unwrap().meta.downgrade(), &ES::new()).to_string())
}

async fn assign(State(state): State<Arc<AppState>>, Json(assign): Json<Assign>) -> Html<std::string::String> {
    let index = if assign.def {
        Index::Let(assign.index)
    } else {
        Index::Param(assign.index)
    };
    let db = DeBruijnIndex(DeBruijn(assign.debruijn), index);
    let mut meta = find_with_id(state.prover.lock().unwrap().meta.downgrade(), assign.meta_id).unwrap();

    let (assn, eqns, _) = test(db, meta.borrow().gamma.sub_es(db.0).linked.unwrap(), meta.clone(), false).unwrap().unwrap();

    meta.borrow_mut().assign(assn, eqns);
    term(State(state)).await
}

async fn unassign(State(state): State<Arc<AppState>>) -> Json<serde_json::Value> {
    Json(json!({ }))
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