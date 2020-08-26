use std::collections::HashMap;
use std::collections::HashSet;
use std::iter;

use itertools::Itertools;

use prusti_interface::specs::typed;
use rustc_middle::mir;
use rustc_middle::ty;

use crate::encoder::places;
use crate::encoder::procedure_encoder::Result;
use crate::encoder::reborrow_signature::ReborrowSignature;
use crate::utils::namespace::Namespace;

use super::ExpirationTool;
use super::ExpirationTools;
use super::MagicWand;
use super::pledges::identify_dependencies;
use super::pledges::PledgeDependenciesSatisfied;
use super::pledges::PledgeWithDependencies;
use super::split_reborrows::split_reborrows;

impl<'tcx> ExpirationTools<'tcx> {
    pub fn construct(
        tcx: ty::TyCtxt<'tcx>,
        mir: &mir::Body<'tcx>,
        reborrows: &ReborrowSignature<places::Place<'tcx>>,
        pledges: Vec<typed::Assertion<'tcx>>
    ) -> Result<Self> {
        let place_mapping = reborrows.blocking.iter().cloned()
            .enumerate().map(|(i, p)| (p, i))
            .collect();

        let namespace = Namespace::new("et");

        let pledges = pledges.into_iter()
            .map(|pledge| {
                let dependants = identify_dependencies(tcx, mir, &reborrows, &pledge)?;
                Ok((pledge, dependants))
            })
            .collect::<Result<Vec<_>>>()?;

        Ok(Self::construct1(namespace, reborrows, &pledges, &place_mapping))
    }

    fn construct1(
        mut namespace: Namespace,
        reborrows: &ReborrowSignature<places::Place<'tcx>>,
        pledges: &[PledgeWithDependencies<'tcx>],
        place_mapping: &HashMap<places::Place<'tcx>, usize>
    ) -> Self {
        split_reborrows(reborrows, pledges.to_vec()).into_iter()
            .sorted_by_key(|(reborrows, _)| reborrows.blocking.iter().min().cloned())
            .map(|(reborrows, pledges)| ExpirationTool::construct2(
                namespace.next_child(), &reborrows, &pledges, place_mapping))
            .collect::<Vec<_>>().into()
    }
}

impl<'tcx> ExpirationTool<'tcx> {
    fn construct2(
        mut namespace: Namespace,
        reborrows: &ReborrowSignature<places::Place<'tcx>>,
        pledges: &[PledgeWithDependencies<'tcx>],
        place_mapping: &HashMap<places::Place<'tcx>, usize>
    ) -> Self {
        let blocking = reborrows.blocking.clone();
        let blocked = reborrows.blocked.clone();

        let mut magic_wands = Vec::new();

        for expired in reborrows.blocking().cloned() {
            let mut namespace = namespace.next_child();

            // Expire the blocking reference and obtain the updated reborrow information.
            let (reborrows, unblocked) = reborrows.expire_output(&expired);

            // The places that expired. Right now, it's just a single one at a time.
            let expired = iter::once(expired).collect::<HashSet<_>>();

            // The assertions that are made available by this magic wand.
            let ripe_pledges = pledges.iter()
                .filter(|(_, dependencies)| dependencies.are_newly_satisfied(
                    &blocking, &blocked, &expired, &unblocked))
                .map(|(assertion, _)| assertion)
                .cloned().collect();

            // The nested expiration tools. Right now there is just a single one, but soon this
            // will be optimized to provide a separate expiration tool for every connected
            // component of the reborrowing graph.
            let expiration_tools = ExpirationTools::construct1(
                namespace.next_child(), &reborrows, pledges, place_mapping);

            let magic_wand = MagicWand {
                namespace,
                expired, unblocked,
                pledges: ripe_pledges,
                expiration_tools
            };
            magic_wands.push(magic_wand);
        }

        // TODO: Have a single "mothership" which stores the place mapping and in every
        //  expiration tool only store a reference to it.
        let place_mapping = place_mapping.clone();

        ExpirationTool { place_mapping, blocking, blocked, magic_wands }
    }
}
