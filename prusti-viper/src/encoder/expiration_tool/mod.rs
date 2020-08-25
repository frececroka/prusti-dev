// TODO: Remove once top-level lib.rs enables warnings.
#![warn(warnings)]

use std::collections::HashMap;
use std::collections::HashSet;

use itertools::Itertools;

use prusti_interface::specs::typed;

use crate::encoder::places;

mod construct;
mod encode;
mod pledges;
mod display;
mod split_reborrows;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Context {
    BeforeExpiry, AfterUnblocked
}

/// A collection of expiration tools, one for every connected component of input/output references.
#[derive(Debug)]
pub struct ExpirationTools<'tcx>(Vec<ExpirationTool<'tcx>>);

/// This is a high-level representation of the nested magic wands that are returned from a
/// re-borrowing function. It has the same structure as the the corresponding Viper expression, but
/// makes the individual components that make up this expression explicit.
#[derive(Debug)]
pub struct ExpirationTool<'tcx> {
    /// A mapping from places to integers that is used to represent places in the Viper encoding.
    pub place_mapping: HashMap<places::Place<'tcx>, usize>,
    /// The places that are still blocking something.
    pub blocking: HashSet<places::Place<'tcx>>,
    /// The places that are still blocked by something.
    pub blocked: HashSet<places::Place<'tcx>>,
    /// The magic wands that can be used to expire the places in `blocking` and unblock the places
    /// in `blocked`. For every reference `r` of `blocking`, there is a magic wand `magic_wands[r]`
    /// that is used to expire `r`.
    magic_wands: Vec<MagicWand<'tcx>>,
}

/// This is a high-level representation of a single magic wand as it appears in the expiration
/// tool. It contains the necessary information to build the left- and right-hand side of the
/// concrete magic wand, but conceptually separated to facilitate manipulation.
#[derive(Debug)]
pub struct MagicWand<'tcx> {
    /// The reference that is expired by applying this magic wand. During encoding, permission for
    /// this will place will make up the left-hand side of the magic wand.
    expired: HashSet<places::Place<'tcx>>,
    /// The references that are immediately unblocked by applying this magic wand. During encoding,
    /// permission for these places will appear on the right-hand side of the magic wand.
    unblocked: HashSet<places::Place<'tcx>>,
    /// The pledges that are made available by applying this magic wand. During encoding, they will
    /// be embedded on the right-hand side of the magic wand.
    pledges: Vec<typed::Assertion<'tcx>>,
    /// The expiration tools that can be used to expire further references. During encoding, they
    /// will be included on the right-hand side of the magic wand.
    expiration_tools: ExpirationTools<'tcx>,
}

impl<'a, 'tcx: 'a> ExpirationTools<'tcx> {
    pub fn blocking(&'a self) -> HashSet<&'a places::Place<'tcx>> {
        self.into_iter().flat_map(|et| &et.blocking).collect()
    }

    pub fn blocked(&'a self) -> HashSet<&'a places::Place<'tcx>> {
        self.into_iter().flat_map(|et| &et.blocked).collect()
    }

    /// Give us the expiration tools that represent the state after all the given places have
    /// expired.
    pub fn expire(&self,
        places: impl IntoIterator<Item=&'a places::Place<'tcx>>
    ) -> &ExpirationTools<'tcx> {
        let mut places = places.into_iter();
        if let Some(place) = places.next() {
            let magic_wand = self.magic_wand(place).unwrap();
            magic_wand.expiration_tools.expire(places)
        } else {
            self
        }
    }

    /// Produces the magic wand that expires the given place.
    fn magic_wand(&self, place: &'a places::Place<'tcx>) -> Option<&MagicWand<'tcx>> {
        self.into_iter()
            .flat_map(|et| et.magic_wands())
            .filter(|mw| mw.expired() == place)
            .next()
    }
}

impl<'tcx> From<Vec<ExpirationTool<'tcx>>> for ExpirationTools<'tcx> {
    fn from(expiration_tools: Vec<ExpirationTool<'tcx>>) -> Self {
        Self(expiration_tools)
    }
}

impl<'a, 'tcx> IntoIterator for &'a ExpirationTools<'tcx> {
    type Item = &'a ExpirationTool<'tcx>;
    type IntoIter = std::slice::Iter<'a, ExpirationTool<'tcx>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'tcx> ExpirationTool<'tcx> {
    /// Creates an iterator over all magic wands that is ordered deterministically. This is
    /// important during the encoding, where the order of conjuncts in magic wands matters.
    fn magic_wands(&self) -> impl Iterator<Item=&MagicWand<'tcx>> {
        self.magic_wands.iter().sorted_by_key(|mw| mw.expired())
    }
}

impl<'tcx> MagicWand<'tcx> {
    /// Returns the reference that is expired by this magic wand. If there is more than one such
    /// reference, it panics.
    fn expired(&self) -> &places::Place<'tcx> {
        assert_eq!(self.expired.len(), 1);
        self.expired.iter().next().unwrap()
    }

    /// Creates an iterator over all unblocked references that is ordered deterministically. This
    /// is important during the encoding, where the order of conjuncts in magic wands matters.
    fn unblocked(&self) -> impl Iterator<Item=&places::Place<'tcx>> {
        self.unblocked.iter().sorted()
    }

    /// Creates an iterator over all pledges that is ordered deterministically. This is important
    /// during the encoding, where the order of conjuncts in magic wands matters.
    fn pledges(&self) -> impl Iterator<Item=&typed::Assertion<'tcx>> {
        // TODO: This is not determinisitc yet.
        self.pledges.iter()
    }

    /// Creates an iterator over all expiration tools that is ordered deterministically. This is
    /// important during the encoding, where the order of conjuncts in magic wands matters.
    fn expiration_tools(&self) -> impl Iterator<Item=&ExpirationTool<'tcx>> {
        self.expiration_tools.into_iter().sorted_by_key(|et| et.blocking.iter().min())
    }
}
