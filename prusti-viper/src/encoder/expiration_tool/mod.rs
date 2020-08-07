use std::collections::HashMap;
use std::hash::Hash;

use itertools::Itertools;

use crate::encoder::places;

mod construct;
mod encode;
mod display;

/// This is a high-level representation of the nested magic wands that are returned from a
/// re-borrowing function. It has the same structure as the the corresponding Viper expression, but
/// makes the individual components that makes up this expression explicit.
#[derive(Debug)]
pub struct ExpirationTool<'tcx> {
    /// A mapping from places to integers that is used to represent places in the Viper encoding.
    pub place_mapping: HashMap<places::Place<'tcx>, usize>,
    /// The places that are still blocking something.
    pub blocking: Vec<places::Place<'tcx>>,
    /// The places that are still blocked by something.
    pub blocked: Vec<places::Place<'tcx>>,
    /// The magic wands that can be used to expire the places in `blocking` and unblock the places
    /// in `blocked`. For every reference `r` of `blocking`, there is a magic wand `magic_wands[r]`
    /// that is used to expire `r`.
    pub magic_wands: HashMap<places::Place<'tcx>, MagicWand<'tcx>>,
}

/// This is a high-level representation of a single magic wand as it appears in the expiration
/// tool. It contains the necessary information to build the left- and right-hand side of the
/// concrete magic wand, but conceptually separated to facilitate manipulation.
#[derive(Debug)]
pub struct MagicWand<'tcx> {
    /// The reference that is expired by applying this magic wand. During encoding, permission for
    /// this will place will make up the left-hand side of the magic wand.
    pub expired: places::Place<'tcx>,
    /// The references that are immediately unblocked by applying this magic wand. During encoding,
    /// permission for these places will appear on the right-hand side of the magic wand.
    pub unblocked: Vec<places::Place<'tcx>>,
    /// The assertions that are made available by applying this magic wand. During encoding, they
    /// will be embedded on the right-hand side of the magic wand.
    // assertions: Vec<Assertion<ET, AT>>,
    /// The expiration tools that can be used to expire further references. During encoding, they
    /// will be included on the right-hand side of the magic wand.
    pub expiration_tools: Vec<ExpirationTool<'tcx>>,
}

impl<'tcx> ExpirationTool<'tcx> {
    /// Creates an iterator over all magic wands that is ordered deterministically. This is
    /// important during the encoding, where the order of conjuncts in magic wands matters.
    fn magic_wands(&self) -> impl Iterator<Item=&MagicWand<'tcx>> {
        self.magic_wands.iter()
            .sorted_by(|(p1, _), (p2, _)| p1.cmp(p2))
            .map(|(_, magic_wand)| magic_wand)
    }
}

impl<'tcx> MagicWand<'tcx> {
    /// Creates an iterator over all unblocked references that is ordered deterministically. This
    /// is important during the encoding, where the order of conjuncts in magic wands matters.
    fn unblocked(&self) -> impl Iterator<Item=&places::Place<'tcx>> {
        self.unblocked.iter().sorted()
    }
}
