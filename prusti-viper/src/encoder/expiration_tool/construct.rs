use std::collections::HashMap;
use std::collections::HashSet;
use std::iter;

use prusti_interface::environment::reborrow_signature::ReborrowSignature;
use prusti_interface::specs::typed;
use rustc_middle::mir;
use rustc_middle::ty;

use crate::encoder::places;

use super::ExpirationTool;
use super::MagicWand;
use super::pledges::identify_dependencies;
use super::pledges::PledgeDependency;
use super::pledges::PledgeDependenciesSatisfied;

type PledgeWithDependencies<'tcx> = (
    typed::Assertion<'tcx>,
    Vec<PledgeDependency<'tcx>>
);

impl<'tcx> ExpirationTool<'tcx> {
    pub fn construct(
        tcx: ty::TyCtxt<'tcx>,
        mir: &mir::Body<'tcx>,
        reborrows: ReborrowSignature<places::Place<'tcx>>,
        pledges: Vec<typed::Assertion<'tcx>>
    ) -> Self {
        let place_mapping = reborrows.blocking.iter().cloned()
            .enumerate().map(|(i, p)| (p, i))
            .collect();

        let pledges = pledges.into_iter()
            .map(|pledge| {
                let dependants = identify_dependencies(tcx, mir, &reborrows, &pledge);
                (pledge, dependants)
            })
            .collect::<Vec<_>>();
        let pledges = pledges.as_slice();

        Self::construct_with_place_mapping(reborrows, pledges, place_mapping)
    }

    fn construct_with_place_mapping(
        reborrows: ReborrowSignature<places::Place<'tcx>>,
        pledges: &[PledgeWithDependencies<'tcx>],
        place_mapping: HashMap<places::Place<'tcx>, usize>
    ) -> Self {
        let blocking = reborrows.blocking.clone();
        let blocked = reborrows.blocked.clone();

        let mut magic_wands = Vec::new();

        for expired in blocking.clone() {
            // Expire the blocking reference and obtain the updated reborrow information.
            let reborrows = reborrows.clone().expire_output(&expired);

            // The places that expired. Right now, it's just a single one at a time.
            let expired = iter::once(expired).collect::<HashSet<_>>();

            // The places unblocked by this expiration.
            let unblocked = reborrows.returned_inputs()
                .into_iter().cloned().collect::<HashSet<_>>();

            let evaluate_lhs = HashSet::new();
            let evaluate_rhs = HashSet::new();

            // The assertions that are made available by this magic wand.
            let ripe_pledges = pledges.iter()
                .filter(|(_, dependencies)| dependencies.are_newly_satisfied(
                    &blocking, &blocked, &expired, &unblocked))
                .map(|(assertion, _)| assertion)
                .cloned().collect();

            // The nested expiration tools. Right now there is just a single one, but soon this
            // will be optimized to provide a separate expiration tool for every connected
            // component of the reborrowing graph.
            let expiration_tool = Self::construct_with_place_mapping(
                reborrows, pledges, place_mapping.clone());
            let expiration_tools = vec![expiration_tool];

            let magic_wand = MagicWand {
                expired, unblocked,
                evaluate_lhs, evaluate_rhs,
                pledges: ripe_pledges,
                expiration_tools
            };
            magic_wands.push(magic_wand);
        }

        ExpirationTool { place_mapping, blocking, blocked, magic_wands }
    }
}
