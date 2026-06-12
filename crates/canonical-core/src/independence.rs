use crate::core::*;
use crate::memory::*;
use std::collections::HashMap;
use union_find::{UnionFind, UnionBySize, QuickUnionUf};

/// The metavariables whose assignments may interact with `mvar`.
pub fn involved(mvar: W<Meta>) -> Vec<W<Meta>> {
    let typ = mvar.borrow().typ.as_ref().unwrap();
    let mut result = typ.1.get_many(&typ.0.borrow().codomain_mvars);
    result.extend(mvar.borrow().gamma.involved());
    for constraint in &mvar.borrow().constraints {
        result.extend(constraint.involved())
    }
    return result;
}

/// Collect the unassigned metavariables in the subtree of `meta` into `out`.
pub fn collect_unassigned(meta: W<Meta>, out: &mut Vec<W<Meta>>) {
    match &meta.borrow().assignment {
        None => out.push(meta.clone()),
        Some(assignment) => {
            for arg in assignment.args.iter() {
                collect_unassigned(arg.downgrade(), out);
            }
        }
    }
}

/// Partition the unassigned metavariables under `root` into independent components.
pub fn split(unassigned: Vec<W<Meta>>) -> Vec<Vec<W<Meta>>> {
    let mut indices = HashMap::new();
    for (i, x) in unassigned.iter().enumerate() {
        indices.insert(x.clone(), i);
    }

    let mut involved_inverse: HashMap<W<Meta>, Vec<W<Meta>>> = HashMap::new();
    for mvar in unassigned.iter() {
        for i in involved(mvar.clone()).iter() {
            if !involved_inverse.contains_key(&i) {
                involved_inverse.insert(i.clone(), Vec::new());
            }
            let arr = involved_inverse.get_mut(i).unwrap();
            if arr.last() != Some(mvar) {
                arr.push(mvar.clone());
            }
        }
    }

    let mut uf = QuickUnionUf::<UnionBySize>::new(unassigned.len());
    for (i, mvar) in unassigned.iter().enumerate() {
        let mut parent = Some(mvar);
        while let Some(p) = parent {
            if let Some(arr) = involved_inverse.get(p) {
                for o in arr {
                    uf.union(i, *indices.get(o).unwrap());
                }
            }
            parent = p.borrow().parent.as_ref().clone();
        }
    }

    let mut buckets: HashMap<usize, Vec<W<Meta>>> = HashMap::new();
    for (i, mvar) in unassigned.iter().enumerate() {
        let r = uf.find(i);
        buckets.entry(r).or_default().push(mvar.clone());
    }
    buckets.into_values().collect()
}
