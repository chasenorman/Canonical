use canonical_compat::ir::*;
use canonical_core::core::*;
use canonical_core::prover::*;
use canonical_core::search::*;
use std::mem::{offset_of, size_of};
use std::panic::{self, AssertUnwindSafe};
use std::ptr;
use std::sync::atomic::Ordering;
use std::sync::mpsc::{self, Sender};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

/*
  Interface with Agda (src/full/Agda/Canonical/FFI.hs).

  Terms are exchanged as trees of #[repr(C)] structs; arrays are (pointer, length)
  pairs of contiguous structs, strings are UTF-8 bytes without terminator.

  - The goal is allocated by Haskell and only borrowed during `canonical_solve`.
  - The result is allocated here and must be released with `canonical_free`.

  With w the size of a pointer, the layout expected by Haskell is checked below.
*/

#[repr(C)]
pub struct FfiStr {
    ptr: *const u8,
    len: usize,
}

#[repr(C)]
pub struct FfiSpine {
    head: FfiStr,
    args: *const FfiExpr,
    nargs: usize,
}

#[repr(C)]
pub struct FfiEquation {
    lhs: FfiSpine,
    rhs: FfiSpine,
    is_redex: u8,
}

#[repr(C)]
pub struct FfiDecl {
    name: FfiStr,
    typ: *const FfiExpr, // null if absent
    equations: *const FfiEquation,
    nequations: usize,
}

#[repr(C)]
pub struct FfiExpr {
    params: *const FfiDecl,
    nparams: usize,
    lets: *const FfiDecl,
    nlets: usize,
    spine: FfiSpine,
}

#[repr(C)]
pub struct FfiResult {
    exprs: *const FfiExpr,
    nexprs: usize,
}

const W: usize = size_of::<usize>();
const _: () = {
    assert!(size_of::<FfiStr>() == 2 * W);
    assert!(size_of::<FfiSpine>() == 4 * W);
    assert!(offset_of!(FfiSpine, args) == 2 * W);
    assert!(size_of::<FfiEquation>() == 9 * W);
    assert!(offset_of!(FfiEquation, rhs) == 4 * W);
    assert!(offset_of!(FfiEquation, is_redex) == 8 * W);
    assert!(size_of::<FfiDecl>() == 5 * W);
    assert!(offset_of!(FfiDecl, typ) == 2 * W);
    assert!(size_of::<FfiExpr>() == 8 * W);
    assert!(offset_of!(FfiExpr, spine) == 4 * W);
    assert!(size_of::<FfiResult>() == 2 * W);
};

// Reading the goal (borrowed from Haskell)

unsafe fn slice<'a, T>(p: *const T, n: usize) -> &'a [T] {
    if n == 0 || p.is_null() {
        &[]
    } else {
        std::slice::from_raw_parts(p, n)
    }
}

unsafe fn read_str(s: &FfiStr) -> String {
    String::from_utf8_lossy(slice(s.ptr, s.len)).into_owned()
}

unsafe fn read_spine(sp: &FfiSpine) -> IRSpine {
    IRSpine {
        head: read_str(&sp.head),
        args: slice(sp.args, sp.nargs).iter().map(|e| read_expr(e)).collect(),
        premise_rules: Vec::new(),
    }
}

unsafe fn read_equation(e: &FfiEquation) -> IREquation {
    IREquation {
        lhs: read_spine(&e.lhs),
        rhs: read_spine(&e.rhs),
        attribution: Vec::new(),
        is_redex: e.is_redex != 0,
    }
}

unsafe fn read_decl(d: &FfiDecl) -> IRDecl {
    IRDecl {
        name: read_str(&d.name),
        typ: d.typ.as_ref().map(|e| read_expr(e)),
        equations: slice(d.equations, d.nequations).iter().map(|e| read_equation(e)).collect(),
    }
}

unsafe fn read_expr(e: &FfiExpr) -> IRExpr {
    IRExpr {
        params: slice(e.params, e.nparams).iter().map(|d| read_decl(d)).collect(),
        lets: slice(e.lets, e.nlets).iter().map(|d| read_decl(d)).collect(),
        spine: read_spine(&e.spine),
        goal_rules: Vec::new(),
    }
}

// Building the result (owned here, released by canonical_free)

fn write_vec<T, U>(xs: &[T], f: impl Fn(&T) -> U) -> (*const U, usize) {
    let b: Box<[U]> = xs.iter().map(f).collect();
    let n = b.len();
    (Box::into_raw(b) as *const U, n)
}

fn write_str(s: &str) -> FfiStr {
    let (ptr, len) = write_vec(s.as_bytes(), |b| *b);
    FfiStr { ptr, len }
}

fn write_spine(sp: &IRSpine) -> FfiSpine {
    let (args, nargs) = write_vec(&sp.args, write_expr);
    FfiSpine { head: write_str(&sp.head), args, nargs }
}

fn write_equation(e: &IREquation) -> FfiEquation {
    FfiEquation { lhs: write_spine(&e.lhs), rhs: write_spine(&e.rhs), is_redex: e.is_redex as u8 }
}

fn write_decl(d: &IRDecl) -> FfiDecl {
    let (equations, nequations) = write_vec(&d.equations, write_equation);
    FfiDecl {
        name: write_str(&d.name),
        typ: match &d.typ {
            None => ptr::null(),
            Some(e) => Box::into_raw(Box::new(write_expr(e))),
        },
        equations,
        nequations,
    }
}

fn write_expr(e: &IRExpr) -> FfiExpr {
    let (params, nparams) = write_vec(&e.params, write_decl);
    let (lets, nlets) = write_vec(&e.lets, write_decl);
    FfiExpr { params, nparams, lets, nlets, spine: write_spine(&e.spine) }
}

unsafe fn free_vec<U>(p: *const U, n: usize, f: impl Fn(&U)) {
    let b = Box::from_raw(ptr::slice_from_raw_parts_mut(p as *mut U, n));
    b.iter().for_each(f);
}

unsafe fn free_str(s: &FfiStr) {
    free_vec(s.ptr, s.len, |_| ());
}

unsafe fn free_spine(sp: &FfiSpine) {
    free_str(&sp.head);
    free_vec(sp.args, sp.nargs, |e| free_expr(e));
}

unsafe fn free_decl(d: &FfiDecl) {
    free_str(&d.name);
    if !d.typ.is_null() {
        let e = Box::from_raw(d.typ as *mut FfiExpr);
        free_expr(&e);
    }
    free_vec(d.equations, d.nequations, |e| {
        free_spine(&e.lhs);
        free_spine(&e.rhs);
    });
}

unsafe fn free_expr(e: &FfiExpr) {
    free_vec(e.params, e.nparams, |d| free_decl(d));
    free_vec(e.lets, e.nlets, |d| free_decl(d));
    free_spine(&e.spine);
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

/// Searches for at most `count` terms of the goal's type, for at most `timeout` seconds.
/// Returns null if the search panicked.
#[no_mangle]
pub unsafe extern "C" fn canonical_solve(goal: *const FfiDecl, timeout: u64, count: usize) -> *mut FfiResult {
    let found = panic::catch_unwind(AssertUnwindSafe(|| {
        let ir_decl = read_decl(&*goal);

        let (tx, rx) = mpsc::channel();
        let arc: Arc<Mutex<Vec<IRExpr>>> = Arc::new(Mutex::new(Vec::new()));
        let arc_clone = arc.clone();
        let (problem, _) = ir_decl.to_problem();
        let prover = Prover::new(problem.downgrade());

        let worker = thread::spawn(move || main(prover, tx, count, arc_clone));
        let _ = rx.recv_timeout(Duration::from_secs(timeout));
        RUN.store(false, Ordering::Relaxed);
        match worker.join() {
            Ok(_) => {
                let v = arc.lock().unwrap();
                let (exprs, nexprs) = write_vec(&v, write_expr);
                FfiResult { exprs, nexprs }
            }
            Err(_) => FfiResult { exprs: ptr::null(), nexprs: 0 },
        }
    }));
    match found {
        Ok(res) => Box::into_raw(Box::new(res)),
        Err(_) => ptr::null_mut(),
    }
}

/// Releases a result returned by `canonical_solve`.
#[no_mangle]
pub unsafe extern "C" fn canonical_free(res: *mut FfiResult) {
    if res.is_null() {
        return;
    }
    let r = Box::from_raw(res);
    if !r.exprs.is_null() {
        free_vec(r.exprs, r.nexprs, |e| free_expr(e));
    }
}
