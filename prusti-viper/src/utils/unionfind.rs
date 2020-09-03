use std::collections::HashMap;
use std::hash::Hash;

pub(crate) fn union<'a, T: Eq + Ord + Hash + Copy + 'a>(
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

pub(crate) fn find<T: Eq + Hash + Copy>(representatives: &HashMap<T, T>, item: T) -> T {
    let &representative = representatives.get(&item).unwrap_or(&item);
    if item == representative {
        item
    } else {
        find(representatives, representative)
    }
}
