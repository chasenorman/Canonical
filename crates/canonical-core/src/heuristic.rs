use crate::search::Next;
use crate::stats::*;

/// Smoothly transitions between `prior` and `a / b` as `b` increases to `breakpoint`.
pub fn div(a: f64, b: f64, prior: f64, breakpoint: f64) -> f64 {
    if b < breakpoint / 2.0 { return prior }
    if b > breakpoint { return a / b }
    let amount = 2.0 * b / breakpoint - 1.0;
    return prior * (1.0 - amount) + (a / b) * amount;
}

/// Selects which metavariable to refine between two options.
pub fn next(first: MetaInfo, second: MetaInfo) -> MetaInfo {
    // Rigid equations are a strict unification constraint, analogous to unit propagation.
    if second.has_rigid_equation { return second }
    if first.has_rigid_equation { return first }

    // The metavariable has over a 50% chance to result in failure of the branch. 
    if div(second.current_stats.failures as f64, second.current_stats.attempts as f64, 0.0, 25.0) > 0.5 { return second }
    if div(first.current_stats.failures as f64, first.current_stats.attempts as f64, 0.0, 25.0) > 0.5 { return first } 

    // One metavariable is significantly more difficult than the other. 
    if second.difficulty() > 3.0 && second.difficulty() > first.difficulty() + 1.0 { return second }
    if first.difficulty() > 3.0 && first.difficulty() > second.difficulty() + 1.0 { return first }

    // Select the later metavariable, so unification can propagate backwards.
    second
}

impl MetaInfo {
    /// The entropy of an unassigned metavariable.
    pub fn difficulty(&self) -> f64 {
        if self.has_rigid_equation { return 1.0 }
        
        // stats consists of only non-rigid while search_stats contains both.
        let prob_non_rigid = div(self.current_stats.attempts as f64, self.future_stats.attempts as f64, 1.0, 100.0);
        let steps_per_completion = div(self.current_stats.steps as f64, self.current_stats.completed_count as f64, 5.0, 100.0);

        // We take the weighted average of 1 and the average number of steps per completion, 
        // weighted by the probability that this metavariable obtains a rigid equation.
        ((1.0 - prob_non_rigid) + prob_non_rigid*steps_per_completion).clamp(1.0, 1000.0)
    }
}

impl AssignmentInfo {
    /// Heuristic penalty for this assignment.
    pub fn tax(&self, next: &Next) -> f64 {
        if self.had_rigid_equation || next.next.is_none() { return 0.0 }

        // Percent of completions to this metavariable that derive from this head assignment.
        let completion_share = div(self.stats.completion_share as f64, self.stats.completion_count as f64, 1.0, 100.0);
        5.0 * (1.0 - completion_share)
    }

    /// Weight between the children of a DFS node.
    pub fn weight(&self) -> f64 {
        1.0
    }
}