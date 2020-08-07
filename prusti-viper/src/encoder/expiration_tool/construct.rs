use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;

use prusti_interface::environment::reborrow_signature::ReborrowSignature;

use crate::encoder::places;

use super::ExpirationTool;
use super::MagicWand;

impl<'tcx> ExpirationTool<'tcx> {
    pub fn construct(reborrows: ReborrowSignature<places::Place<'tcx>>) -> Self {
        let place_mapping = reborrows.blocking.iter().cloned()
            .enumerate().map(|(i, p)| (p, i))
            .collect();
        Self::construct_with_place_mapping(reborrows, place_mapping)
    }

    fn construct_with_place_mapping(
        reborrows: ReborrowSignature<places::Place<'tcx>>,
        place_mapping: HashMap<places::Place<'tcx>, usize>
    ) -> Self {
        let blocking = reborrows.blocking.clone().into_iter().collect::<Vec<_>>();
        let blocked = reborrows.blocked.clone().into_iter().collect::<Vec<_>>();

        let mut magic_wands = HashMap::new();

        for blocking in &blocking {
            let updated_reborrows = reborrows.clone().expire_output(blocking);
            let expired = blocking.clone();
            let unblocked = updated_reborrows.returned_inputs().into_iter().cloned().collect();
            let expiration_tool = Self::construct_with_place_mapping(
                updated_reborrows, place_mapping.clone());
            let expiration_tools = vec![expiration_tool];
            let magic_wand = MagicWand { expired, unblocked, expiration_tools };
            magic_wands.insert(blocking.clone(), magic_wand);
        }

        ExpirationTool { place_mapping, blocking, blocked, magic_wands }
    }
}
