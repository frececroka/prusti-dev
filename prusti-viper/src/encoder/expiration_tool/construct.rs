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
use super::ExpirationToolCarrier;
use super::ExpirationTools;
use super::pledges::identify_dependencies;
use super::pledges::PledgeDependenciesSatisfied;
use super::pledges::PledgeWithDependencies;
use super::split_reborrows::split_reborrows;

impl<'c, 'tcx> ExpirationToolCarrier<'c, 'tcx> {
    pub fn construct(&'c mut self,
        tcx: ty::TyCtxt<'tcx>,
        mir: &mir::Body<'tcx>,
        reborrows: &ReborrowSignature<places::Place<'tcx>>,
        pledges: Vec<typed::Assertion<'tcx>>
    ) -> Result<&'c ExpirationTools<'c, 'tcx>> {
        self.place_mapping = reborrows.blocking.iter().cloned()
            .enumerate().map(|(i, p)| (p, i))
            .collect();
        let shared_self = &*self;
        let pledges = pledges.into_iter()
            .map(|pledge| {
                let pledge = shared_self.add_pledge(pledge);
                let dependants = identify_dependencies(tcx, mir, &reborrows, pledge)?;
                Ok((pledge, dependants))
            })
            .collect::<Result<Vec<_>>>()?;
        let namespace = Namespace::new("et");
        Ok(ExpirationTools::construct(self, reborrows, &pledges, namespace))
    }
}

impl<'c, 'tcx> ExpirationTools<'c, 'tcx> {
    fn construct(
        carrier: &'c ExpirationToolCarrier<'c, 'tcx>,
        reborrows: &ReborrowSignature<places::Place<'tcx>>,
        pledges: &[PledgeWithDependencies<'c, 'tcx>],
        mut namespace: Namespace,
    ) -> &'c Self {
        let expiration_tools = split_reborrows(reborrows, pledges.to_vec()).into_iter()
            .sorted_by_key(|(reborrows, _)| reborrows.blocking.iter().min().cloned())
            .map(|(reborrows, pledges)| ExpirationTool::construct(
                carrier, &reborrows, &pledges, namespace.next_child()))
            .collect::<Vec<_>>().into();
        carrier.add_expiration_tools(expiration_tools)
    }
}

impl<'c, 'tcx> ExpirationTool<'c, 'tcx> {
    fn construct(
        carrier: &'c ExpirationToolCarrier<'c, 'tcx>,
        reborrows: &ReborrowSignature<places::Place<'tcx>>,
        pledges: &[PledgeWithDependencies<'c, 'tcx>],
        mut namespace: Namespace,
    ) -> &'c Self {
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
                .map(|(pledge, _)| pledge)
                .cloned().collect();

            // The nested expiration tools.
            let expiration_tools = ExpirationTools::construct(
                carrier, &reborrows, pledges, namespace.next_child());

            magic_wands.push(carrier.add_magic_wand(
                namespace,
                expired, unblocked,
                ripe_pledges,
                expiration_tools
            ));
        }

        carrier.add_expiration_tool(blocking, blocked, magic_wands)
    }
}
