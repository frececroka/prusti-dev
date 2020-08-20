use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;

use itertools::Itertools;

use crate::encoder::places;
use crate::encoder::reborrow_signature::ReborrowSignature;

use super::pledges::PledgeWithDependencies;

pub(super) fn split_reborrows<'tcx>(
    reborrow_signature: &ReborrowSignature<places::Place<'tcx>>,
    pledges: Vec<PledgeWithDependencies<'tcx>>
) -> Vec<(ReborrowSignature<places::Place<'tcx>>, Vec<PledgeWithDependencies<'tcx>>)> {
    let mut representatives = HashMap::new();

    // Merge all sets A, B where A contains a blocking reference r and B contains a reference
    // blocked by r.
    for blocking in &reborrow_signature.blocking {
        for blocked in reborrow_signature.reborrows(blocking) {
            union(&mut representatives, &[blocking, blocked]);
        }
    }

    // For every pledge, join all sets that contain references that this pledge depends upon.
    for (_, dependencies) in &pledges {
        let dependencies = dependencies.iter()
            .map(|pd| &pd.place)
            .collect::<Vec<_>>();
        union(&mut representatives, dependencies);
    }

    // Group the edges `(blocking, blocked)` of the re-borrow graph by the set that `blocking`
    // belongs to.
    let mut reborrows = reborrow_signature.reborrows.clone().into_iter()
        .sorted_by_key(|(blocking, _)| find(&representatives, blocking).clone())
        .group_by(|(blocking, _)| find(&representatives, blocking).clone())
        .into_iter()
        .map(|(key, items)| (key, items.collect::<HashMap<_, _>>()))
        .collect::<HashMap<_, _>>();

    // Group the pledges `(assertion, dependencies)` by the set that every dependency from
    // `dependencies` belongs to (all dependencies of a pledge should belong to the same set).
    let mut pledges = pledges.clone().into_iter()
        .group_by(|(_, dependencies)| {
            let representatives = dependencies.iter()
                .map(|dependency| find(&representatives, &dependency.place).clone())
                .collect::<HashSet<_>>();
            assert_eq!(representatives.len(), 1);
            representatives.into_iter().next().unwrap()
        }).into_iter()
        .map(|(key, items)| (key, items.collect::<Vec<_>>()))
        .collect::<HashMap<_, _>>();

    // Gather the representatives for all the sets.
    let representatives = representatives.keys()
        .map(|place| find(&representatives, place))
        .collect::<HashSet<_>>();

    // Turn every set into a re-borrow signature with pledges.
    representatives.iter()
        .filter_map(|representative| {
            let reborrows = reborrows.remove(representative).unwrap_or(HashMap::new());
            if reborrows.len() > 0 {
                let mutability = reborrow_signature.mutability.clone();
                let reborrow_signature = ReborrowSignature::new(mutability, reborrows);
                let pledges = pledges.remove(representative).unwrap_or(Vec::new());
                Some((reborrow_signature, pledges))
            } else { None }
        })
        .collect()
}

fn union<'a, T: Eq + Ord + Hash + Copy + 'a>(
    representatives: &mut HashMap<T, T>,
    items: impl AsRef<[T]>
) {
    let items = items.as_ref().into_iter()
        .map(|&item| find(representatives, item))
        .collect::<Vec<_>>();
    let &representative = items.iter().min().unwrap();
    for item in items {
        representatives.insert(item, representative);
    }
}

fn find<T: Eq + Hash + Copy>(representatives: &HashMap<T, T>, item: T) -> T {
    let &representative = representatives.get(&item).unwrap_or(&item);
    if item == representative {
        item
    } else {
        find(representatives, representative)
    }
}
