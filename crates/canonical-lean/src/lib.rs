// https://github.com/leanprover/lean4/blob/master/src/include/lean/lean.h
use std::ffi::{CStr, CString, c_char, c_void};
use canonical_compat::ir::*;
use canonical_core::core::*;
use canonical_core::prover::*;
use canonical_core::search::*;
use canonical_core::memory::S;
use std::thread;
use std::time::{Duration, Instant};
use std::sync::atomic::Ordering;
use std::sync::mpsc::{self, Sender};
use std::sync::{Mutex, Arc, Condvar};
use once_cell::sync::Lazy;
use canonical_compat::refine::*;
use tokio::runtime::Runtime;
// use std::fs::OpenOptions;
// use std::io::Write;

#[repr(C)]
pub struct LeanObject {
    m_rc: i32,
    m_cs_sz: u16,
    m_other: u8,
    m_tag: u8,
}

fn lean_is_scalar(o: *const LeanObject) -> bool {
    (o as usize) & 1 == 1
}

fn lean_box(n: usize) -> *const LeanObject {
    ((n << 1) | 1) as *const LeanObject
}

fn lean_unbox(o: *const LeanObject) -> usize {
    (o as usize) >> 1
}

fn lean_obj_tag(o: *const LeanObject) -> usize {
    if lean_is_scalar(o) {
        lean_unbox(o)
    } else {
        unsafe { (*o).m_tag as usize }
    }
}

#[repr(C)]
pub struct LeanStringObject {
    m_header: LeanObject,
    m_size: usize,
    m_capacity: usize,
    m_length: usize,
    // m_data: [c_char; 0],
}

fn to_string(s: *const LeanStringObject) -> String {
    unsafe {
        assert!((*s).m_header.m_tag == 249);
        let ptr = (s as *const c_char).add(std::mem::size_of::<LeanStringObject>());
        CStr::from_ptr(ptr).to_string_lossy().into_owned()
    }
}

fn to_lean_string(s: &str) -> *const LeanStringObject {
    let c_str = CString::new(s).unwrap().into_raw();
    unsafe { lean_mk_string(c_str as *const i8) }
}

#[repr(C)]
pub struct LeanArrayObject {
    m_header: LeanObject,
    m_size: usize,
    m_capacity: usize,
    // m_data: [*const LeanObject; 0]
}

fn to_vec(arr: *const LeanArrayObject) -> Vec<*const LeanObject> {
    unsafe {
        assert!((*arr).m_header.m_tag == 246);
        let ptr = (arr as *const u8).add(std::mem::size_of::<LeanArrayObject>()) as *const *const LeanObject;
        (0..(*arr).m_size).map(|i| *ptr.add(i)).collect()
    }
}

fn to_lean_array(v: &Vec<*const LeanObject>) -> *const LeanArrayObject {
    unsafe {
        let capacity = v.len();
        let sz = std::mem::size_of::<LeanArrayObject>() + std::mem::size_of::<*const LeanObject>() * capacity;
        let o = lean_alloc_object(sz) as *mut LeanArrayObject;
        (*o).m_header = LeanObject { m_rc: 1, m_cs_sz: 0, m_other: 0, m_tag: 246 };
        (*o).m_size = capacity;
        (*o).m_capacity = capacity;
        let ptr = (o as *const u8).add(std::mem::size_of::<LeanArrayObject>()) as *mut *const LeanObject;
        for (i, x) in v.iter().enumerate() {
            ptr.add(i).write(*x);
        }
        o
    }
}

#[repr(C)]
pub struct LeanCtorObject {
    m_header: LeanObject
    // m_objs: [*const LeanObject; 0]
}

fn lean_align(v: usize, a: usize) -> usize {
    (v / a) * a + a * (if v % a != 0 { 1 } else { 0 }) 
}

// fn lean_get_slot_idx(sz: usize) -> usize {
//     assert!(sz > 0);
//     assert!(lean_align(sz, 8) == sz);
//     sz / 8 - 1
// }

fn lean_alloc_small_object(sz: usize) -> *mut LeanObject {
    let sz = lean_align(sz, 8);
    unsafe {
        let mem = mi_malloc_small(sz);
        if mem.is_null() {
            lean_internal_panic_out_of_memory();
        }
        let o = mem as *mut LeanObject;
        (*o).m_cs_sz = sz as u16;
        return o;
    }
}

fn lean_alloc_ctor_memory(sz: usize) -> *mut LeanCtorObject {
    let sz1 = lean_align(sz, 8);
    let r = lean_alloc_small_object(sz);
    unsafe {
        if sz1 > sz {
            let end = (r as *const u8).add(sz1) as *mut usize;
            end.sub(1).write(0);
        }
    }
    return r as *mut LeanCtorObject;
}

#[repr(C)]
pub struct LeanOption {
    m_header: LeanObject,
    val: *const LeanObject
}

fn to_option(o: *const LeanOption) -> Option<*const LeanObject> {
    unsafe {
        if lean_is_scalar(o as *const LeanObject) {
            assert!(lean_unbox(o as *const LeanObject) == 0);
            None
        } else {
            Some((*o).val)
        }
    }
}

// fn to_lean_option(opt: &Option<*const LeanObject>) -> *const LeanOption {
//     unsafe {
//         match opt {
//             None => lean_box(0) as *const LeanOption,
//             Some(x) => {
//                 let o = lean_alloc_ctor(1, 1, 0) as *mut LeanOption;
//                 (*o).val = *x;
//                 o
//             }
//         }
//     }
// }

fn lean_alloc_ctor(tag: usize, num_objs: usize, scalar_sz: usize) -> *mut LeanCtorObject {
    assert!(tag <= 244);
    assert!(num_objs < 256);
    assert!(scalar_sz < 1024);
    let sz = std::mem::size_of::<LeanCtorObject>() + std::mem::size_of::<*const LeanObject>() * num_objs + scalar_sz;
    let o = lean_alloc_ctor_memory(sz);
    unsafe {
        (*o).m_header = LeanObject { m_rc: 1, m_cs_sz: 0, m_other: num_objs as u8, m_tag: tag as u8 };
    }
    o
}

#[repr(C)]
pub struct LeanVar {
    m_header: LeanObject,
    name: *const LeanStringObject,
    irrelevant: bool
}

fn to_ir_var(v: *const LeanVar) -> IRVar {
    unsafe {
        IRVar {
            name: to_string((*v).name),
            irrelevant: (*v).irrelevant
        }
    }
}

fn to_lean_var(v: &IRVar) -> *const LeanVar {
    unsafe {
        let o = lean_alloc_ctor(0, 1, 1) as *mut LeanVar;
        (*o).name = to_lean_string(&v.name);
        (*o).irrelevant = v.irrelevant;
        o
    }
}

#[repr(C)]
pub struct LeanDefinition {
    m_header: LeanObject,
    term: *const LeanTerm,
}

#[repr(C)]
pub struct LeanConstructor {
    m_header: LeanObject,
    type_name: *const LeanStringObject,
    index: usize,
    args_start: usize
}

#[repr(C)]
pub struct LeanRecursor {
    m_header: LeanObject,
    type_name: *const LeanStringObject,
    rules: *const LeanArrayObject,
    shared: usize,
    major: usize
}

#[repr(C)]
pub struct LeanProjection {
    m_header: LeanObject,
    type_name: *const LeanStringObject,
    index: usize,
    major: usize
}

#[repr(C)]
pub struct LeanHasMajor {
    m_header: LeanObject,
    major: usize
}

fn to_ir_value(value: *const LeanObject) -> IRValue {
    unsafe { match lean_obj_tag(value) {
        0 => {
            let defn = value as *const LeanDefinition;
            IRValue::Definition(to_ir_term((*defn).term))
        }
        1 => {
            let ctor = value as *const LeanConstructor;
            IRValue::Constructor(to_string((*ctor).type_name), (*ctor).index, (*ctor).args_start)
        }
        2 => {
            let rec = value as *const LeanRecursor;
            let rules = to_vec((*rec).rules).iter().map(|x| to_ir_term(*x as *const LeanTerm)).collect();
            IRValue::Recursor(to_string((*rec).type_name), (*rec).shared, (*rec).major, rules)
        }
        3 => {
            let proj = value as *const LeanProjection;
            IRValue::Projection(to_string((*proj).type_name), (*proj).index, (*proj).major)
        }
        _ => IRValue::Opaque
    } }
}

fn to_lean_value(value: &IRValue) -> *const LeanObject {
    unsafe { match value {
        IRValue::Definition(term) => {
            let o = lean_alloc_ctor(0, 1, 0) as *mut LeanDefinition;
            (*o).term = to_lean_term(term);
            o as *const LeanObject
        }
        IRValue::Constructor(type_name, index, args_start) => {
            let o = lean_alloc_ctor(1, 1, std::mem::size_of::<usize>()*2) as *mut LeanConstructor;
            (*o).type_name = to_lean_string(type_name);
            (*o).index = *index;
            (*o).args_start = *args_start;
            o as *const LeanObject
        }
        IRValue::Recursor(type_name, shared, major, rules) => {
            let rules = to_lean_array(&rules.iter().map(|x| to_lean_term(x) as *const LeanObject).collect());
            let o = lean_alloc_ctor(2, 2, std::mem::size_of::<usize>()*2) as *mut LeanRecursor;
            (*o).type_name = to_lean_string(type_name);
            (*o).rules = rules;
            (*o).shared = *shared;
            (*o).major = *major;
            o as *const LeanObject
        }
        IRValue::Projection(type_name, index, major) => {
            let o = lean_alloc_ctor(3, 1, std::mem::size_of::<usize>()*2) as *mut LeanProjection;
            (*o).type_name = to_lean_string(type_name);
            (*o).index = *index;
            (*o).major = *major;
            o as *const LeanObject
        }
        IRValue::Opaque => lean_box(4)
    } }
}

#[repr(C)]
pub struct LeanLet {
    m_header: LeanObject,
    name: *const LeanStringObject,
    value: *const LeanObject,
    irrelevant: bool
}

fn to_ir_let(l: *const LeanLet) -> IRLet {
    unsafe {
        IRLet {
            var: IRVar {
                name: to_string((*l).name),
                irrelevant: (*l).irrelevant
            },
            value: to_ir_value((*l).value)
        }
    }
}

fn to_lean_let(d: &IRLet) -> *const LeanLet {
    unsafe {
        let o = lean_alloc_ctor(0, 2, 1) as *mut LeanLet;
        (*o).name = to_lean_string(&d.var.name);
        (*o).irrelevant = d.var.irrelevant;
        (*o).value = to_lean_value(&d.value);
        o
    }
}

#[repr(C)]
pub struct LeanTerm {
    m_header: LeanObject,
    params: *const LeanArrayObject,
    lets: *const LeanArrayObject,
    head: *const LeanStringObject,
    args: *const LeanArrayObject
}

fn to_ir_term(term: *const LeanTerm) -> IRTerm {
    unsafe {
        IRTerm {
            params: to_vec((*term).params).iter().map(|x| to_ir_var(*x as *const LeanVar)).collect(),
            lets: to_vec((*term).lets).iter().map(|x| to_ir_let(*x as *const LeanLet)).collect(),
            head: to_string((*term).head),
            args: to_vec((*term).args).iter().map(|x| to_ir_term(*x as *const LeanTerm)).collect()
        }
    }
}

fn to_lean_term(term: &IRTerm) -> *const LeanTerm {
    unsafe {
        let o = lean_alloc_ctor(0, 4, 0) as *mut LeanTerm;
        (*o).params = to_lean_array(&term.params.iter().map(|x| to_lean_var(x) as *const LeanObject).collect());
        (*o).lets = to_lean_array(&term.lets.iter().map(|x| to_lean_let(x) as *const LeanObject).collect());
        (*o).head = to_lean_string(&term.head);
        (*o).args = to_lean_array(&term.args.iter().map(|x| to_lean_term(x) as *const LeanObject).collect());
        o
    }
}

#[repr(C)]
pub struct LeanType {
    m_header: LeanObject,
    params: *const LeanArrayObject,
    lets: *const LeanArrayObject,
    codomain: *const LeanTerm
}

fn to_ir_type(t: *const LeanType) -> IRType {
    unsafe {
        IRType {
            params: to_vec((*t).params).iter().map(|x| 
                to_option(*x as *const LeanOption).map(|t| to_ir_type(t as *const LeanType))).collect(),
            lets: to_vec((*t).lets).iter().map(|x| 
                to_option(*x as *const LeanOption).map(|t| to_ir_type(t as *const LeanType))).collect(),
            codomain: to_ir_term((*t).codomain)
        }
    }
}

// fn to_lean_type(t: &IRType) -> *const LeanType {
//     unsafe {
//         let o = lean_alloc_ctor(0, 3, 0) as *mut LeanType;
//         (*o).params = to_lean_array(&t.params.iter().map(|x| to_lean_option(&x.as_ref().map(|t| 
//             to_lean_type(&t) as *const LeanObject)) as *const LeanObject).collect());
//         (*o).lets = to_lean_array(&t.lets.iter().map(|x| 
//             to_lean_option(&x.as_ref().map(|t| to_lean_type(&t) as *const LeanObject)) as *const LeanObject).collect());
//         (*o).codomain = to_lean_term(&t.codomain);
//         o
//     }
// }

#[repr(C)]
pub struct CanonicalResult {
    m_header: LeanObject,
    terms: *const LeanArrayObject,
    attempted_resolutions: u32,
    successful_resolutions: u32,
    steps: u32,
    last_level_steps: u32,
    branching: f32
}

fn to_lean_result(terms: *const LeanArrayObject, result: DFSResult, last_level_steps: u32) -> *const CanonicalResult {
    unsafe {
        let scalar_sz = std::mem::size_of::<u32>()*4 + std::mem::size_of::<f32>();
        let o = lean_alloc_ctor(0, 1, scalar_sz) as *mut CanonicalResult;
        (*o).terms = terms;
        (*o).attempted_resolutions = result.attempts;
        (*o).successful_resolutions = result.steps + result.unknown_count;
        (*o).steps = result.steps;
        (*o).last_level_steps = last_level_steps;
        (*o).branching = result.branching as f32 / result.steps as f32;
        o
    }
}

extern "C" {
    fn lean_mk_string(s: *const i8) -> *const LeanStringObject;
    fn lean_alloc_object(sz: usize) -> *const LeanObject;
    // fn lean_alloc_small(sz: usize, slot_idx: usize) -> *const LeanObject;
    fn lean_io_check_canceled_core() -> bool;
    fn mi_malloc_small(sz: usize) -> *mut c_void;
    fn lean_internal_panic_out_of_memory();
    // fn lean_dbg_trace(s: *const LeanStringObject, f: *const LeanObject);
}

/// `termToString` in Lean.
#[no_mangle]
pub extern "C" fn term_to_string(term: *const LeanTerm) -> *const LeanStringObject {
    to_lean_string(&to_ir_term(term).to_string())
}

/// `typToString` in Lean.
#[no_mangle]
pub extern "C" fn typ_to_string(t: *const LeanType) -> *const LeanStringObject {
    to_lean_string(&to_ir_type(t).to_string())
}

/// Starts a `Prover` on `ir_type`, appending solutions to `terms` and sending on `sender` once complete.
fn main(ir_type: IRType, sender: Sender<()>, program_synthesis: bool, count: usize, terms: Arc<Mutex<Vec<IRTerm>>>) -> (DFSResult, u32) {
    let tb = ir_type.to_type(&ES::new());
    let entry = &tb.codomain.borrow().gamma.linked.as_ref().unwrap().borrow().node.entry;
    let node = Node { 
        entry: Entry { params_id: entry.params_id, lets_id: entry.lets_id, subst: None, 
            context: Some(Context(tb.types.downgrade(), tb.codomain.borrow().gamma.clone(), tb.codomain.borrow().bindings.clone()))}, 
        bindings: tb.codomain.borrow().gamma.linked.as_ref().unwrap().borrow().node.bindings.clone() 
    };
    let mut owned_linked = Vec::new();
    let es = ES::new().append(node, &mut owned_linked);
    let tb_ref = S::new(tb);
    let problem_bind = S::new(Bind { name: "proof".to_string(), irrelevant: false, value: Value::Opaque, major: false });
    let ty = Type(tb_ref.downgrade(), es, problem_bind.downgrade());
    let prover = Prover::new(ty, program_synthesis);

    prover.prove(&|term: Term| {
        let mut v = terms.lock().unwrap();
        let ir_term = IRTerm::from_term(term.base, &ES::new());
        if v.len() < count && v.iter().all(|x| x != &ir_term) {
            v.push(ir_term);
        }
        if v.len() >= count {
            RUN.store(false, Ordering::Relaxed);
            sender.send(()).unwrap();
        }
    }, false)
}

pub struct Lock {
    locked: Mutex<bool>,
    cvar: Condvar,
}

impl Lock {
    pub fn new() -> Self {
        Self {
            locked: Mutex::new(false),
            cvar: Condvar::new(),
        }
    }

    pub fn lock(&self) {
        let mut guard = self.locked.lock().unwrap();
        while *guard {
            guard = self.cvar.wait(guard).unwrap();
        }
        *guard = true;
    }

    pub fn unlock(&self) {
        let mut guard = self.locked.lock().unwrap();
        *guard = false;
        self.cvar.notify_one();
    }
}

/// This lock ensures that we only have one instance running at a time.
static INSTANCE: Lazy<Lock> = Lazy::new(|| Lock::new());

/// `canonical` in Lean.
#[no_mangle]
pub unsafe extern "C" fn canonical(typ: *const LeanType, timeout: u64, count: usize, prog_synth: bool, debug: bool) -> *const CanonicalResult {
    INSTANCE.lock();
    let ir_type = to_ir_type(typ);
    if debug {
        ir_type.save("debug.json".to_string());
    }
    let (tx, rx) = mpsc::channel();

    let arc : Arc<Mutex<Vec<IRTerm>>> = Arc::new(Mutex::new(Vec::new()));
    let arc_clone = arc.clone();
    let worker = thread::spawn(move || {
        main(ir_type, tx, prog_synth, count, arc_clone)
    });

    // Regularly check whether the task has been cancelled from Lean, until the timout is reached. 
    let start = Instant::now();
    while start.elapsed() < Duration::from_secs(timeout) {
        match rx.recv_timeout(Duration::from_millis(10)) {
            Err(mpsc::RecvTimeoutError::Timeout) => {
                if lean_io_check_canceled_core() || !RUN.load(Ordering::Relaxed) {
                    break;
                }
            }
            _ => break,
        }
    }

    RUN.store(false, Ordering::Relaxed);
    let (result, last_level_steps) = worker.join().unwrap();

    let v = arc.lock().unwrap();
    let terms = to_lean_array(&v.iter().map(|x| to_lean_term(x) as *const LeanObject).collect());

    INSTANCE.unlock();
    to_lean_result(terms, result, last_level_steps)
}

#[no_mangle]
pub unsafe extern "C" fn refine(typ: *const LeanType, prog_synth: bool) -> bool {
    let ir_type = to_ir_type(typ);
    let tb = ir_type.to_type(&ES::new());
    let entry = &tb.codomain.borrow().gamma.linked.as_ref().unwrap().borrow().node.entry;
    let node = Node { 
        entry: Entry { params_id: entry.params_id, lets_id: entry.lets_id, subst: None, 
            context: Some(Context(tb.types.downgrade(), tb.codomain.borrow().gamma.clone(), tb.codomain.borrow().bindings.clone()))}, 
        bindings: tb.codomain.borrow().gamma.linked.as_ref().unwrap().borrow().node.bindings.clone() 
    };
    let mut owned_linked = Vec::new(); // must be stored
    let es = ES::new().append(node, &mut owned_linked);
    let tb_ref = S::new(tb); // must be stored
    let problem_bind = S::new(Bind { name: "proof".to_string(), irrelevant: false, value: Value::Opaque, major: false }); // must be stored
    let ty = Type(tb_ref.downgrade(), es, problem_bind.downgrade());
    let prover = Prover::new(ty, prog_synth);

    match GLOBAL_STATE.get() {
        None => {
            let state = AppState {
                prover: Mutex::new(prover),
                assigned: Mutex::new(Vec::new()),
                _owned_linked: Mutex::new(owned_linked),
                _owned_tb: Mutex::new(tb_ref),
                _owned_bind: Mutex::new(problem_bind)
            };
            thread::spawn(move || { 
                Runtime::new().unwrap().block_on(async {
                    start_server(state).await;
                });
            });
        }
        Some(state) => {
            *state.prover.lock().unwrap() = prover;
            state.assigned.lock().unwrap().clear();
            *state._owned_linked.lock().unwrap() = owned_linked;
            *state._owned_tb.lock().unwrap() = tb_ref;
            *state._owned_bind.lock().unwrap() = problem_bind;
        }
    }
    return true;
}

// fn print_force(s: String) -> Result<(), std::io::Error> {
//     let mut file = OpenOptions::new()
//         .append(true)
//         .create(true)
//         .open("output.txt")?;

//     file.write(s.as_bytes())?;
//     file.write(b"\n")?;
//     file.flush()?;
//     Ok(())
// }
