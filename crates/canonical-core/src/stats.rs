use crate::core::*;
use crate::memory::*;
use crate::search::*;
use std::sync::{Arc, atomic::{AtomicU32, Ordering}};
use arc_swap::ArcSwap;
use hashbrown::HashMap;
use once_cell::sync::Lazy;
use crate::prover::NUM_JOBS;
use thread_local_collect::tlm::probed::{Control, Holder};
use std::thread::ThreadId;

/// Tracks the number of DFS node visits performed, for debugging.
pub static STEP_COUNT: AtomicU32 = AtomicU32::new(0);

/// Global map from metavariable bucket to `MetaStats`. 
pub static META_MAP: Lazy<ArcSwap<HashMap<usize, MetaStats>>> = Lazy::new(|| ArcSwap::from_pointee(HashMap::new()));
pub static META_CONTROL: Lazy<Control<HashMap<usize, MetaStats>, HashMap<usize, MetaStats>>> = 
    Lazy::new(|| Control::new(&LOCAL_META_MAP, HashMap::new(), HashMap::new, meta_op));

/// Global map from assignment bucket to `AssignmentStats`
pub static ASSIGNMENT_MAP: Lazy<ArcSwap<HashMap<usize, AssignmentStats>>> = Lazy::new(|| ArcSwap::from_pointee(HashMap::new()));
pub static ASSIGNMENT_CONTROL: Lazy<Control<HashMap<usize, AssignmentStats>, HashMap<usize, AssignmentStats>>> = 
    Lazy::new(|| Control::new(&LOCAL_ASSIGNMENT_MAP, HashMap::new(), HashMap::new, assignment_op));


thread_local! {
    /// Local maps where statistics are tabulated. These will be periodically accumulated into the global maps. 
    pub static LOCAL_META_MAP: Holder<HashMap<usize, MetaStats>, HashMap<usize, MetaStats>> = Holder::new();
    pub static LOCAL_ASSIGNMENT_MAP: Holder<HashMap<usize, AssignmentStats>, HashMap<usize, AssignmentStats>> = Holder::new();
}

/// Reduce operation for `LOCAL_META_MAP`s.  
pub fn meta_op(data: HashMap<usize, MetaStats>, acc: &mut HashMap<usize, MetaStats>, _: ThreadId) {
    for (key, stats) in data {
        acc.entry(key).or_insert_with(MetaStats::new).add(stats);
    }
}

/// Reduce operation for `LOCAL_ASSIGNMENT_MAP`s.  
pub fn assignment_op(data: HashMap<usize, AssignmentStats>, acc: &mut HashMap<usize, AssignmentStats>, _: ThreadId) {
    for (key, stats) in data {
        acc.entry(key).or_insert_with(AssignmentStats::new).add(stats);
    }
}

/// The information that may be used to select the next metavariable to refine. 
pub struct MetaInfo {
    pub meta: W<Meta>,
    pub has_rigid_equation: bool,
    bin: usize,
    /// The `MetaStats` for `bin`.
    pub current_stats: MetaStats,
    /// The sum of `stats` for all possible future bins of this metavariable. 
    pub future_stats: MetaStats
}

impl MetaInfo {
    /// Collect the information of a metavaraible. 
    pub fn new(meta: W<Meta>) -> Self {
        let has_rigid_equation = meta.borrow().equations.iter().any(|e| 
            e.premise.whnf(&mut Vec::new(), false).1.is_some() || 
            e.goal.whnf(&mut Vec::new(), false).1.is_some()
        );
        let bin = meta.borrow().typ.as_ref().unwrap().0.usize() + has_rigid_equation as usize;
        let current_stats = META_MAP.load().get(&bin).map(|x| x.clone()).unwrap_or_else(MetaStats::new);
        let mut future_stats = if has_rigid_equation { MetaStats::new() } else {
            let rigid_bin = meta.borrow().typ.as_ref().unwrap().0.usize() + 1;
            META_MAP.load().get(&rigid_bin).map(|x| x.clone()).unwrap_or_else(MetaStats::new)
        };
        future_stats.add(current_stats.clone());

        MetaInfo { meta, has_rigid_equation, bin, current_stats, future_stats }
    }
    
    /// Adds new statistics information to the original `bin` of this metavariable.
    pub fn log(&self, result: &DFSResult, entropy_gain: f64, info: &SearchInfo) {
        META_CONTROL.with_data_mut(|map| 
            map.entry(self.bin).or_insert_with(MetaStats::new).accumulate(result, entropy_gain, info));
    }
}

/// Tracks various statistics of a metavariable.
/// `lifetime` values accumulate from metavariable creation to deletion.
/// `dfs` values accumulate over the DFS subtree rooted when the metavariable is next.
/// `assignment` values accumulate over the DFS subtree after the metavariable is given an assignment.
#[derive(Clone)]
pub struct SearchInfo {
    pub dfs_steps: f64,
    pub lifetime_steps: f64,
    pub lifetime_attempts: u32,
    pub dfs_completed: bool,
    pub assignment_completed: bool
}

impl SearchInfo {
    /// The `SearchInfo` of a new metavariable.
    pub fn new() -> Self {
        SearchInfo { dfs_steps: 0.0, lifetime_steps: 0.0, lifetime_attempts: 0, dfs_completed: false, assignment_completed: false }
    }
    
    /// Add `info` into `self`.
    pub(crate) fn add(&mut self, info: &SearchInfo) {
        self.lifetime_steps += info.lifetime_steps;
        self.lifetime_attempts += info.lifetime_attempts;
        self.dfs_steps += info.dfs_steps;
        self.dfs_completed = self.dfs_completed || info.dfs_completed;
        self.assignment_completed = self.assignment_completed || info.assignment_completed;
    }

    /// Reset statistics related to being the next metavariable.
    pub(crate) fn dfs_fence(&mut self) {
        self.dfs_steps = 0.0;
        self.dfs_completed = false;
        self.assignment_completed = false;
    }

    /// Reset statistics related to an assignment.
    pub(crate) fn assignment_fence(&mut self) {
        self.assignment_completed = false;
    }
}

/// Statistics for a metavariable bin. 
#[derive(Clone, Debug)]
pub struct MetaStats {
    pub steps: f64,
    pub completed_count: u32,

    pub attempts: u32,
    pub failures: u32,
    pub log_entropy_gain: f64
}

impl MetaStats {
    /// `MetaStats` with no information. 
    pub fn new() -> Self {
        MetaStats { steps: 0.0, attempts: 0, failures: 0, log_entropy_gain: 0.0, completed_count: 0 }
    }

    /// Add the `result` from the DFS subtree and the metavariable lifetime `info` to the statistics.
    fn accumulate(&mut self, result: &DFSResult, entropy_gain: f64, info: &SearchInfo) {
        self.attempts += 1;
        self.steps += info.dfs_steps;
        if info.dfs_completed {
            self.completed_count += 1;
        }
        self.log_entropy_gain += entropy_gain.ln_1p();
        if result.unknown_count == 0 {
            self.failures += 1;
        }
    }
    
    /// Add `stats` into `self`.
    pub fn add(&mut self, stats: MetaStats) {
        self.steps += stats.steps;
        self.attempts += stats.attempts;
        self.failures += stats.failures;
        self.log_entropy_gain += stats.log_entropy_gain;
        self.completed_count += stats.completed_count;
    }
}

/// The information that may be used to determine the entropy of an assignment. 
pub struct AssignmentInfo {
    pub meta: W<Meta>,
    pub equations_generated: usize,
    pub had_rigid_equation: bool,
    pub has_rigid_type: bool,
    bin: usize,
    pub stats: AssignmentStats
}

impl AssignmentInfo {
    /// Collect the information of an assignment. 
    pub fn new(meta: W<Meta>) -> Self {
        let equations_generated = meta.borrow().assignment.as_ref().unwrap().changes.len();
        let had_rigid_equation = meta.borrow().has_rigid_equation;
        let has_rigid_type = meta.borrow().assignment.as_ref().unwrap().has_rigid_type;
        let bin = meta.borrow().typ.as_ref().unwrap().0.usize() // + had_rigid_equation as usize 
                       + meta.borrow().assignment.as_ref().unwrap().bind.usize() + (has_rigid_type as usize) << 1;
        let stats = ASSIGNMENT_MAP.load().get(&bin).map(|x| x.clone()).unwrap_or_else(AssignmentStats::new);
        
        AssignmentInfo { meta, equations_generated, had_rigid_equation, has_rigid_type, bin, stats }
    }

    /// Adds new statistics information to the original `bin` of this assignment.
    pub fn log(&self, result: &DFSResult, completion_share: bool, ever_completed: bool) {
        ASSIGNMENT_CONTROL.with_data_mut(|map| 
            map.entry(self.bin).or_insert_with(AssignmentStats::new).accumulate(result, completion_share, ever_completed));
    }
}

/// Statistics for an assignment bin. 
#[derive(Clone)]
pub struct AssignmentStats {
    pub count: u32,
    pub completion_count: u32,
    pub completion_share: u32,
    pub bushiness: f64
}

impl AssignmentStats {
    /// `AssignmentStats` with no information.
    pub fn new() -> Self {
        AssignmentStats { count: 0, completion_count: 0, completion_share: 0, bushiness: 0.0 }
    }

    /// Add the `result` from the DFS subtree to the statistics.
    fn accumulate(&mut self, result: &DFSResult, completion_share: bool, ever_completed: bool) {
        self.count += 1;
        self.bushiness += result.unknown_count as f64 / (result.steps + result.unknown_count) as f64;
        if ever_completed {
            self.completion_count += 1;
            if completion_share {
                self.completion_share += 1;
            }
        }
    }
    
    /// Add `stats` into `self`.
    pub fn add(&mut self, stats: AssignmentStats) {
        self.count += stats.count;
        self.completion_count += stats.completion_count;
        self.completion_share += stats.completion_share;
        self.bushiness += stats.bushiness;
    }
}

/// Reset all statistics information.
pub fn reset() {
    // If we are not careful to only keep one instance of Canonical running, the following line may hang.
    RUN.store(true, Ordering::Release);
    META_CONTROL.take_tls();
    META_CONTROL.take_acc(HashMap::new());
    META_MAP.store(Arc::new(HashMap::new()));
    ASSIGNMENT_CONTROL.take_tls();
    ASSIGNMENT_CONTROL.take_acc(HashMap::new());
    ASSIGNMENT_MAP.store(Arc::new(HashMap::new()));
    NUM_JOBS.store(0, Ordering::Release);
}