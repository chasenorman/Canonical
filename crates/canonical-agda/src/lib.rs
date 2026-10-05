use canonical_compat::ir::*;
use canonical_core::core::*;
use canonical_core::prover::*;
use canonical_core::search::*;
use serde::{Deserialize, Serialize};
use std::ops::Deref;
use std::sync::atomic::Ordering;
use std::sync::mpsc::{self, Sender};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;
use std::{
    ffi::{c_char, CStr, CString},
    str::FromStr,
};

#[derive(Serialize, Deserialize, Debug)]
struct HSpine {
    head: String,
    args: Vec<HExpr>,
}

#[derive(Serialize, Deserialize, Debug)]
struct HEquation {
    lhs: HSpine,
    rhs: HSpine,
    is_redex: bool,
}
#[derive(Serialize, Deserialize, Debug)]
struct HDecl {
    name: String,
    typ: Option<HExpr>,
    equations: Vec<HEquation>,
}

#[derive(Serialize, Deserialize, Debug)]
struct HExpr {
    params: Vec<HDecl>,
    lets: Vec<HDecl>,
    spine: HSpine,
}

fn to_ir_spine(sp: &HSpine) -> IRSpine {
    IRSpine {
        head: sp.head.to_owned(),
        args: sp.args.iter().map(to_ir_expr).collect(),
        premise_rules: Vec::new(),
    }
}

fn to_ir_expr(e: &HExpr) -> IRExpr {
    IRExpr {
        params: e.params.iter().map(to_ir_decl).collect(),
        lets: e.lets.iter().map(to_ir_decl).collect(),
        spine: to_ir_spine(&e.spine),
        goal_rules: Vec::new(),
    }
}

fn to_ir_decl(d: &HDecl) -> IRDecl {
    IRDecl {
        name: d.name.to_owned(),
        typ: match &d.typ {
            None => None,
            Some(d) => Some(to_ir_expr(&d)),
        },
        equations: d.equations.iter().map(to_ir_equation).collect(),
    }
}

fn to_ir_equation(e: &HEquation) -> IREquation {
    IREquation {
        lhs: to_ir_spine(&e.lhs),
        rhs: to_ir_spine(&e.rhs),
        attribution: Vec::new(),
        is_redex: e.is_redex,
    }
}

fn to_hdecl(d: &IRDecl) -> HDecl {
    HDecl {
        name: d.name.to_owned(),
        typ: match &d.typ {
            None => None,
            Some(e) => Some(to_hexpr(&e)),
        },
        equations: d.equations.iter().map(to_hequation).collect(),
    }
}

fn to_hspine(s: &IRSpine) -> HSpine {
    HSpine {
        head: s.head.to_owned(),
        args: s.args.iter().map(to_hexpr).collect(),
    }
}

fn to_hequation(e: &IREquation) -> HEquation {
    HEquation {
        lhs: to_hspine(&e.lhs),
        rhs: to_hspine(&e.rhs),
        is_redex: e.is_redex,
    }
}

fn to_hexpr(e: &IRExpr) -> HExpr {
    HExpr {
        params: e.params.iter().map(to_hdecl).collect(),
        lets: e.lets.iter().map(to_hdecl).collect(),
        spine: to_hspine(&e.spine),
    }
}

fn main(
    prover: Prover,
    sender: Sender<()>,
    count: usize,
    terms: Arc<Mutex<Vec<IRExpr>>>,
) -> (DFSResult, u32) {
    prover.prove(
        &|term: Term| {
            let mut v = terms.lock().unwrap();
            let bindings = term
                .base
                .borrow()
                .gamma
                .linked
                .as_ref()
                .unwrap()
                .borrow()
                .node
                .bindings
                .clone();
            let ir_term = IRExpr::from_lambda::<false>(term, bindings, false);
            if v.len() < count && v.iter().all(|x| x != &ir_term) {
                v.push(ir_term);
            }
            if v.len() >= count {
                RUN.store(false, Ordering::Relaxed);
                sender.send(()).unwrap();
            }
        },
        false,
    )
}

#[no_mangle]
pub extern "C" fn canonical(goal: *const c_char, timeout: u64, count: usize) -> *mut c_char {
    unsafe {
        let cstr = CStr::from_ptr(goal).to_str().unwrap();
        let goal: HDecl =
            serde_json::from_str(cstr).expect("Failed to convert the JSON to a type.\n");

        let ir_decl = to_ir_decl(&goal);

        let (tx, rx) = mpsc::channel();

        let arc: Arc<Mutex<Vec<IRExpr>>> = Arc::new(Mutex::new(Vec::new()));
        let arc_clone = arc.clone();
        // let mut owned_linked = Vec::new();
        let (problem, _) = ir_decl.to_problem();
        let prover = Prover::new(problem.downgrade());

        let worker = thread::spawn(move || main(prover, tx, count, arc_clone));
        let _ = rx.recv_timeout(Duration::from_secs(timeout));
        RUN.store(false, Ordering::Relaxed);
        let res: Vec<HExpr> = match worker.join() {
            Ok((_, _)) => {
                let v = arc.lock().unwrap();
                v.deref().iter().map(to_hexpr).collect()
            }
            Err(_) => Vec::new(),
        };
        let json = serde_json::to_string(&res).expect("Failed to convert type to a JSON format.\n");
        let cstr2 =
            CString::from_str(&json.as_str()).expect("Failed to convert JSON to a C string.\n");
        cstr2.into_raw()
    }
}
