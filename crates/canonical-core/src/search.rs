use crate::core::*;
use crate::heuristic::*;
use crate::memory::{S, W, WVec};
use crate::stats::*;
use std::sync::atomic::AtomicBool;

/// Set `RUN` to false to cancel terminate the ongoing problem. 
pub static RUN: AtomicBool = AtomicBool::new(true);

/// Results from a DFS subtree. 
pub struct DFSResult {
    pub unknown_count: u32,
    pub solution_count: u32,
    pub steps: u32,
    pub entropy: f64,
    pub branching: usize,
    pub attempts: u32
}

impl DFSResult {
    /// Add `other` into `self`.
    pub fn add(&mut self, other: Self) {
        self.unknown_count += other.unknown_count;
        self.steps += other.steps;
        self.solution_count += other.solution_count;
        self.branching += other.branching;
        self.attempts += other.attempts;
    }
}

/// Construct and test the `Assignment` from refining `meta` with `head`.
pub fn test(head: DeBruijnIndex, curr: W<Linked>, mut meta: W<Meta>) -> Option<Option<(Assignment, Vec<Equation>, Vec<RedexConstraint>, AssignmentInfo)>> {
    let context = curr.borrow().node.entry.context.as_ref().unwrap();
    let Some(tb) = &context.0.borrow()[head.1] else {
        // Variable does not have a type, we are not permitted to apply it.
        return None;
    };
    let args: Vec<S<Meta>> = tb.borrow().args_metas(Some(meta.clone()));
    let gamma = meta.borrow().gamma.clone();
    let mut _owned_linked = Vec::new();
    let var_type = curr.borrow().node.entry.context.as_ref().unwrap().get(head.1, Entry::subst(Subst(WVec::new(&args), gamma.clone())), &mut _owned_linked);

    meta.borrow_mut().assignment = Some(Assignment {
        head, args, bind: var_type.2.clone(), changes: Vec::new(), redex_changes: Vec::new(), _owned_linked,
        has_rigid_type: matches!(var_type.codomain().whnf::<true, ()>(&mut Vec::new(), &mut ()).1, Head::Var(_)),
        var_type: Some(var_type.clone()),
    });

    let Some((eqns, redexes)) = meta.clone().borrow_mut().test_assignment(meta.clone()) else {
        // Equation violation. 
        meta.borrow_mut().assignment = None;
        return Some(None);
    };
    
    let assignment_info = AssignmentInfo::new(meta.clone());
    let mut assignment = meta.borrow_mut().assignment.take().unwrap();

    // Calculate the `typ` and `gamma` of the new metavariables.
    for i in 0..tb.borrow().types.borrow().params.len() {
        let arg = assignment.args[i].borrow_mut(); 
        let var_id = next_u64();
        let let_id = next_u64();
        let typ = var_type.params().get(Index::Param(i), 
            Entry { params_id: var_id, lets_id: let_id, subst: None, context: None }, &mut assignment._owned_linked
        );
        arg.gamma = gamma.append(Node { 
            entry: Entry { params_id: var_id, lets_id: let_id, subst: None, context: Some(typ.params()) }, 
            bindings: arg.bindings.clone() 
        }, &mut assignment._owned_linked);
        arg.typ = Some(typ);
    }
    Some(Some((assignment, eqns, redexes, assignment_info)))
}

/// Result from traversing the partial term, including the metavariable to be refined next and the entropy. 
pub struct Next {
    pub next: Option<MetaInfo>,
    pub meta_entropy: f64,
    pub tree_entropy: f64,
    size: u32,
}

impl Next {
    /// Construct a `Next` with the product of the entropy and selecting the more preferable of the two metavariables. 
    fn accumulate(self, other: Self) -> Next {
        let next = match (self.next, other.next) {
            (None, next) | (next, None) => next,
            (Some(meta1), Some(meta2)) => Some(next(meta1, meta2))
        };
        Next { next, meta_entropy: self.meta_entropy * other.meta_entropy, size: self.size + other.size, tree_entropy: self.tree_entropy * other.tree_entropy }
    }

    /// Returns a clone of `self` adding entropy from an assignment. 
    fn assigned_entropy(self, entropy: f64, tax: f64) -> Next {
        Next { next: self.next, meta_entropy: self.meta_entropy, size: self.size, tree_entropy: (self.tree_entropy + tax) * entropy }
    }
    
    /// Checks whether the entropy is above the depth threshold. 
    pub fn exceeds(&self, max_entropy: f64, max_size: u32) -> bool {
        max_entropy < self.entropy() || self.size >= max_size
    }
    
    /// The total entropy is the entropy induced by assignments multiplied by the entropy induced by metavariables.
    pub(crate) fn entropy(&self) -> f64 {
        self.meta_entropy * self.tree_entropy
    }
}

impl Meta {
    /// Traverse the partial term, to obtain the entropy and next metavariable.
    pub fn next(mut meta: W<Meta>) -> Next {
        match &meta.borrow().assignment {
            None => { 
                // The entropy of a metavariable is the difficulty.
                let meta_info = MetaInfo::new(meta.clone());
                Next { meta_entropy: meta_info.difficulty(), next: Some(meta_info), size: 0, tree_entropy: 1.0 }
            }
            Some(Assignment { args, .. }) => {
                // The entropy of an assignment is the branching factor, with added tax.
                let acc = args.iter().fold(Next { next: None, meta_entropy: 1.0, size: 1, tree_entropy: 1.0 }, 
                    |acc, meta| acc.accumulate(Meta::next(meta.downgrade())));
                if acc.next.is_none() {
                    meta.borrow_mut().stats_buffer.dfs_completed = true;
                }
                // We performed the recursive calls first so that `acc` contains complete subtree information. 
                let tax = AssignmentInfo::new(meta.clone()).tax(&acc);
                acc.assigned_entropy(meta.borrow().branching, tax)
            }
        }
    }
}

