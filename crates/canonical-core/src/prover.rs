use crate::search::*;
use crate::core::*;
use crate::memory::*;
use crate::stats::*;
use rayon::prelude::*;
use std::sync::atomic::{Ordering, AtomicUsize};
use std::sync::Arc;
use hashbrown::HashMap;

/// The number of Rayon jobs yet to be completed.
pub static NUM_JOBS: AtomicUsize = AtomicUsize::new(0);

/// A `Prover` has a metavariable for the main goal, and a flag for `program_synthesis` mode.
pub struct Prover {
    pub meta: S<Meta>,
    /// In case we only want to solve a subtree of `meta`, this defines the root for `next`.
    pub next_root: W<Meta>
}

unsafe impl Send for Prover {}
unsafe impl Send for W<Meta> {}

impl Prover {
    /// Creates a new Prover for the specified `Type`. 
    pub fn new(typ: Type) -> Self {
        let meta = S::new(Meta::new(typ));
        Prover { next_root: meta.downgrade(), meta }
    }

    /// Gets the current (partial) term of the prover. 
    pub fn get_term(&self) -> Term {
        Term { base: self.meta.downgrade(), es: self.meta.borrow().gamma.clone() }
    }

    /// Start proof search, with a callback for solutions.
    pub fn prove<F>(&self, callback: &F, verbose: bool) -> (DFSResult, u32) where F: Fn(Term) + Send + Sync {
        reset();
        let mut depth = 1e4;
        let mut previous_steps = 0;
        let mut acc = DFSResult { unknown_count: 0, steps: 0, entropy: 1.0, solution_count: 0, attempts: 0, branching: 0 };
        
        // Iterative deepening. 
        while RUN.load(Ordering::Relaxed) {
            if verbose { println!("entropy (log): {}", (depth as f32).ln_1p()); }
            let result = self.parallel_dfs(depth, (depth.ln_1p()*4.0) as u32, callback);
            if verbose { println!("ratio: {}", result.steps as f32 / previous_steps as f32); }
            
            previous_steps = result.steps;
            depth *= 3.0;

            // Update the global statistics maps.
            META_MAP.store(Arc::new(META_CONTROL.probe_tls()));
            ASSIGNMENT_MAP.store(Arc::new(ASSIGNMENT_CONTROL.probe_tls()));
            
            // If all branches were fully explored, we can terminate.
            let fail = result.unknown_count == 0;
            acc.add(result);
            if fail { 
                RUN.store(false, Ordering::Relaxed);
                return (acc, previous_steps)
            }
        }
        (acc, previous_steps)
    }

    /// Parallelized DFS, up to an entropy of `max_entropy` and term size of `max_size`. Solutions are passed to the `callback`.
    pub fn parallel_dfs<F>(&self, max_entropy: f64, max_size: u32, callback: &F) -> DFSResult where F: Fn(Term) + Send + Sync {
        if !RUN.load(Ordering::Relaxed) {
            // The task has been cancelled. 
            return DFSResult { unknown_count: 0, steps: 0, entropy: 1.0, solution_count: 0, attempts: 0, branching: 0 };
        }
        
        let mut next_result = Meta::next(self.next_root.clone());
        let exceeds = next_result.exceeds(max_entropy, max_size);
        let Some(next) = next_result.next.as_mut() else {
            // No metavariables left, send the solution to the callback.
            callback(self.get_term());
            return DFSResult { unknown_count: 0, steps: 0, entropy: 1.0, solution_count: 1, attempts: 0, branching: 0 };
        };

        if exceeds { 
            // Partial terms exceeds the depth threshold, consider the branch result unknown. 
            return DFSResult { unknown_count: 1, steps: 0, entropy: next_result.meta_entropy, solution_count: 0, attempts: 0, branching: 0 };
        }

        // Start an attempt for next.
        next.meta.borrow_mut().has_rigid_equation = next.has_rigid_equation;
        next.meta.borrow_mut().stats.dfs_fence();
        next.meta.borrow_mut().stats_buffer.dfs_fence();
        next.meta.borrow_mut().stats_buffer.lifetime_attempts += 1;

        // STEP_COUNT.fetch_add(1, Ordering::Relaxed);
        
        let mut options = Vec::new();
        let mut total_weight = 0.0;
        let mut attempts = 0;
        let base_id = next.meta.borrow().typ.as_ref().unwrap().0.borrow().id;
        for (db, linked) in next.meta.borrow().gamma.iter_unify(base_id) {
            let attempt = test(db, linked, next.meta.clone());
            if attempt.is_some() {
                attempts += 1;
            }
            if let Some(Some(result)) = attempt {
                total_weight += result.3.weight();
                options.push(result);
            }
        }
        let branching = options.len();
        next.meta.borrow_mut().stats_buffer.dfs_steps = options.len() as f64;

        let mut results = Vec::new();
        let mut iter = options.into_iter();
        let num_jobs = NUM_JOBS.load(Ordering::Relaxed);

        if branching < 2 || next_result.tree_entropy > 1000.0 || num_jobs > 100 {
            while let Some((assignment, equations, redex_constraints, info)) = iter.next() {
                let meta = next.meta.borrow_mut();

                meta.assign(assignment, equations, redex_constraints);

                // Start assignment statistics.
                meta.stats.assignment_fence();
                meta.stats_buffer.assignment_fence();

                meta.branching = total_weight / info.weight();
                let result = self.parallel_dfs(max_entropy, max_size, callback);
                
                // The steps spent on this metavariable 
                for child in meta.assignment.as_ref().unwrap().args.iter() {
                    meta.stats_buffer.dfs_steps += child.borrow().stats.lifetime_steps + child.borrow().stats_buffer.lifetime_steps;
                }

                // End assignment statistics.
                meta.stats.assignment_fence();
                meta.stats_buffer.assignment_fence();
                
                meta.unassign();
                // If there are more than two remaining options, this option took many steps, 
                // and there are less than 100 jobs, execute the remaining options in parallel.
                let parallel = iter.len() > 2 && result.steps > (num_jobs*100) as u32 && num_jobs < 100;
                results.push((result, info, next.meta.borrow().stats.assignment_completed 
                                         || next.meta.borrow().stats_buffer.assignment_completed));
                if parallel { break }
            }
        }

        // Create cloned provers for each remaining option. 
        let provers: Vec<(Prover, W<Meta>, AssignmentInfo)> = iter.filter_map(
            |(assignment, equations, redex_constraints, info)| {
            next.meta.borrow_mut().assign(assignment, equations, redex_constraints);

            next.meta.borrow_mut().branching = total_weight / info.weight();
            let result = self.try_clone();

            next.meta.borrow_mut().unassign();
            result.map(|(prover, map)| (prover, map.get(&next.meta).unwrap().clone(), info))
        }).collect();
        NUM_JOBS.fetch_add(provers.len(), Ordering::Acquire);

        // Parallel iteration over remaining options. 
        let more_results: Vec<(DFSResult, Prover, f64, AssignmentInfo, bool)> = provers.into_par_iter().map(
            |(prover, translated_meta, info)| {
            let result = prover.parallel_dfs(max_entropy, max_size, callback);
            NUM_JOBS.fetch_sub(1, Ordering::Relaxed);
            let mut steps = 0.0;
            for child in translated_meta.borrow().assignment.as_ref().unwrap().args.iter() {
                steps += child.borrow().stats.lifetime_steps + child.borrow().stats_buffer.lifetime_steps;
            }
            let assignment_completed = translated_meta.borrow().stats.assignment_completed 
                                          || translated_meta.borrow().stats_buffer.assignment_completed;
            (result, prover, steps, info, assignment_completed)
        }).collect();

        // Accumulate the parallel results into self.
        for (result, prover, steps, info, assignment_completed) in more_results {
            self.accumulate(prover);
            results.push((result, info, assignment_completed));
            next.meta.borrow_mut().stats_buffer.dfs_steps += steps;
        }
        
        // Accumulate statistics over sequential and parallel branches.
        let mut acc = DFSResult { unknown_count: 0, steps: 1, entropy: next_result.meta_entropy, solution_count: 0, branching, attempts };
        let mut weighted_entropy_gain = 0.0;
        let mut max_steps = 0;
        for (result, info, assignment_completed) in results {
            info.log(&result, assignment_completed, next.meta.borrow().stats.dfs_completed 
                                                                                  || next.meta.borrow().stats_buffer.dfs_completed);
            weighted_entropy_gain += (result.entropy / next_result.meta_entropy) * (result.steps as f64);
            if result.steps > max_steps { max_steps = result.steps }
            acc.add(result);
        }
        let effective_branching_factor = if max_steps == 0 { 1.0 } else { acc.steps as f64 / max_steps as f64 };

        next.meta.borrow_mut().stats_buffer.lifetime_steps += next.meta.borrow().stats_buffer.dfs_steps + next.meta.borrow().stats.dfs_steps;
        let mut stats = next.meta.borrow().stats.clone();
        stats.add(&next.meta.borrow().stats_buffer);

        // End the attempt for next. 
        next.meta.borrow_mut().stats.dfs_fence();
        next.meta.borrow_mut().stats_buffer.dfs_fence();

        next.log(&acc, weighted_entropy_gain / (acc.steps as f64 * effective_branching_factor), &stats);
        acc
    }

    /// Return a clone of this prover and a map of metavariables between this and the new clone, with `stats_buffer` moved into `stats`.
    pub fn try_clone(&self) -> Option<(Self, HashMap<W<Meta>, W<Meta>>)> {
        Meta::try_clone(self.meta.downgrade()).map(|(meta, map)| {
            (Prover { meta, next_root: map.get(&self.next_root).unwrap().clone() }, map)
        })
    }

    /// Accumulate the statistics of `other` into self. 
    fn accumulate(&self, other: Prover) {
        accumulate_stats(self.meta.downgrade(), other.meta.downgrade());
    }
}


/// Transfer the assignment and stats from `from` to `to`. Returns the translation of `meta`, if present. 
pub fn transfer(from: W<Meta>, mut to: W<Meta>, map: &mut HashMap<W<Meta>, W<Meta>>) -> bool {
    to.borrow_mut().stats.add(&from.borrow().stats);
    to.borrow_mut().stats.add(&from.borrow().stats_buffer);
    to.borrow_mut().has_rigid_equation = from.borrow().has_rigid_equation;
    to.borrow_mut().branching = from.borrow().branching;
    map.insert(from.clone(), to.clone());

    let Some(from_assn) = &from.borrow().assignment else { return true; };
    
    let sub_es = to.borrow().gamma.sub_es(from_assn.head.0);
    let Some(Some((to_assn, eqns, redex_constraints, _info))) = 
        test(from_assn.head, sub_es.linked.unwrap(), to.clone()) else { 
            return false; 
        };
    
    to.borrow_mut().assign(to_assn, eqns, redex_constraints);

    from_assn.args.iter().zip(to.borrow().assignment.as_ref().unwrap().args.iter()).all(
        |(from_child, to_child)|
        transfer(from_child.downgrade(), to_child.downgrade(), map)
    )
}

/// Accumulate the statistics of `from` into `to`.
fn accumulate_stats(mut to: W<Meta>, from: W<Meta>) {
    to.borrow_mut().stats_buffer.add(&from.borrow().stats_buffer);
    if to.borrow().assignment.is_none() { return; }

    let zipped_args = to.borrow().assignment.as_ref().unwrap().args.iter()
        .zip(from.borrow().assignment.as_ref().unwrap().args.iter());
    for (to_child, from_child) in zipped_args {
        accumulate_stats(to_child.downgrade(), from_child.downgrade());
    }
}

impl Meta {
    /// Return a clone of this metvariable and a map of metavariables between this and the new clone, with `stats_buffer` moved into `stats`.
    pub fn try_clone(meta: W<Meta>) -> Option<(S<Meta>, HashMap<W<Meta>, W<Meta>>)> {
        let new = S::new(Meta::new(meta.borrow().typ.as_ref().unwrap().clone()));
        let mut map = HashMap::new();
        if transfer(meta, new.downgrade(), &mut map) {
            return Some((new, map))
        }
        return None
    }
}