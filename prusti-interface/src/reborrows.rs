use std::collections::{HashMap, HashSet};

use environment::borrowck::facts;
use environment::borrowck::facts::Interner;
use environment::borrowck::facts::Point;
use environment::borrowck::facts::PointType;
use rustc::mir;
use rustc::mir::BasicBlock;
use rustc::mir::Mir;
use rustc::mir::Operand;
use rustc::mir::Place;
use rustc::mir::Projection;
use rustc::mir::ProjectionElem;
use rustc::mir::Rvalue;
use rustc::mir::TerminatorKind;
use rustc::mir::visit::Visitor;
use rustc::ty::TypeVariants;
use rustc_data_structures::indexed_vec::Idx;

const EMTPY_BASIC_BLOCKS: &[BasicBlock] = &[];

pub fn infer_reborrows(
    mir: &Mir,
    interner: &Interner,
    borrow_regions: &[(facts::Region, facts::Loan, facts::PointIndex)]
) -> HashMap<facts::Loan, HashSet<facts::Loan>> {
    let cfg = Cfg::new(mir);
    let place_to_loans = determine_place_to_loans(mir, interner, borrow_regions);
    let place_to_loans = &fixpoint_place_to_loans(mir, &cfg, place_to_loans);
    let reborrows = HashMap::new();
    let mut state = DetermineReborrows {
        mir, interner, borrow_regions, place_to_loans, reborrows
    };
    state.visit_mir(mir);
    state.reborrows
}

struct DetermineReborrows<'a, 'tcx: 'a> {
    mir: &'a Mir<'tcx>,
    interner: &'a Interner,
    borrow_regions: &'a [(facts::Region, facts::Loan, facts::PointIndex)],
    place_to_loans: &'a HashMap<BasicBlock, HashMap<Place<'tcx>, HashSet<facts::Loan>>>,
    reborrows: HashMap<facts::Loan, HashSet<facts::Loan>>
}

impl<'a, 'tcx> DetermineReborrows<'a, 'tcx> {

    fn loans_at(&self, location: mir::Location) -> Vec<facts::Loan> {
        loans_at(self.interner, self.borrow_regions, location)
    }

    fn add_reborrows_for_place(&mut self,
        block: BasicBlock,
        loan: facts::Loan,
        place: &Place<'tcx>
    ) {
        if let Some(reborrowed_loans) = self.place_to_loans[&block].get(place) {
            for &reborrowed_loan in reborrowed_loans {
                self.add_reborrow(loan, reborrowed_loan);
            }
        }
    }

    fn add_reborrow(&mut self, from: facts::Loan, to: facts::Loan) {
        self.reborrows.entry(from).or_default().insert(to);
    }

}

impl<'a, 'tcx> mir::visit::Visitor<'tcx> for DetermineReborrows<'a, 'tcx> {

    fn visit_assign(&mut self,
        block: BasicBlock,
        _: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        location: mir::Location
    ) {
        let loans = self.loans_at(location);

        // Obtain the loan that is created by this assignment.
        let loan = match loans.len() {
            0 => return,
            1 => loans[0],
            _ => unreachable!()
        };

        match rvalue {
            Rvalue::Ref(_, _, place) =>
                if let Some(deref) = dereferenced_places(place).first() {
                    self.add_reborrows_for_place(block, loan, deref);
                },
            Rvalue::Use(Operand::Move(place)) |
            Rvalue::Use(Operand::Copy(place)) =>
                self.add_reborrows_for_place(block, loan, place),
            _ => {}
        }
    }

    fn visit_terminator_kind(&mut self,
        block: BasicBlock,
        terminator: &mir::TerminatorKind<'tcx>,
        location: mir::Location
    ) {
        let args = match terminator {
            TerminatorKind::Call { ref args, .. } => args,
            _ => return
        };

        let ref_args = get_ref_args(self.mir, args);
        let loans = self.loans_at(location);

        let (lhs_loan, arg_loans) = if loans.len() == ref_args.len() + 1 {
            // The function returns a reference.
            (Some(loans[0]), &loans[1..])
        } else if loans.len() == ref_args.len() {
            // The function doesn't return a reference.
            (None, &loans[..])
        } else {
            unreachable!()
        };

        if let Some(lhs_loan) = lhs_loan {
            for &arg_loan in arg_loans {
                self.add_reborrow(lhs_loan, arg_loan);
            }
        }

        // The loans that represent the references moved into the function
        // re-borrow the places that are moved.
        for (arg, arg_loan) in ref_args.iter().zip(arg_loans) {
            self.add_reborrows_for_place(block, *arg_loan, arg);
        }
    }

}

fn dereferenced_places<'a, 'tcx>(place: &'a Place<'tcx>) -> Vec<&'a Place<'tcx>> {
    match place {
        Place::Projection(box Projection { base, elem }) => {
            let mut derefs = dereferenced_places(base);
            match elem {
                ProjectionElem::Deref => derefs.push(base),
                _ => {}
            }
            derefs
        },
        _ => Vec::new(),
    }
}

fn determine_place_to_loans<'tcx>(
    mir: &Mir<'tcx>,
    interner: &Interner,
    borrow_regions: &[(facts::Region, facts::Loan, facts::PointIndex)]
) -> HashMap<BasicBlock, HashMap<Place<'tcx>, HashSet<facts::Loan>>> {
    let place_to_loans = HashMap::new();
    let mut state = DeterminePlaceToLoans { mir, interner, borrow_regions, place_to_loans };
    state.visit_mir(mir);
    state.place_to_loans
}

struct DeterminePlaceToLoans<'a, 'tcx: 'a> {
    mir: &'a Mir<'tcx>,
    interner: &'a Interner,
    borrow_regions: &'a [(facts::Region, facts::Loan, facts::PointIndex)],
    place_to_loans: HashMap<BasicBlock, HashMap<Place<'tcx>, HashSet<facts::Loan>>>
}

impl<'a, 'tcx> DeterminePlaceToLoans<'a, 'tcx> {

    fn loans_at(&self, location: mir::Location) -> Vec<facts::Loan> {
        loans_at(self.interner, self.borrow_regions, location)
    }

    fn set_loans_at_place(&mut self,
        block: BasicBlock,
        place: &Place<'tcx>,
        loan: facts::Loan
    ) {
        let loans_at_place = self.place_to_loans
            .entry(block).or_default()
            .entry(place.clone()).or_default();

        // We're overwriting the place, so all old loans are cleared.
        loans_at_place.clear();

        // The newly created loan is associated with the RHS place.
        loans_at_place.insert(loan);
    }

}

impl<'a, 'tcx> mir::visit::Visitor<'tcx> for DeterminePlaceToLoans<'a, 'tcx> {

    fn visit_assign(&mut self,
        block: BasicBlock,
        place: &Place<'tcx>,
        _: &Rvalue<'tcx>,
        location: mir::Location
    ) {
        let loans = self.loans_at(location).to_vec();
        if !loans.is_empty() {
            assert_eq!(loans.len(), 1);
            self.set_loans_at_place(block, place, loans[0]);
        }
    }

    fn visit_terminator_kind(&mut self,
        block: BasicBlock,
        terminator: &TerminatorKind<'tcx>,
        location: mir::Location
    ) {
        let destination_place = match terminator {
            TerminatorKind::Call { destination: Some((ref place, _)), .. } => place,
            _ => return
        };

        let local = match destination_place {
            Place::Local(local) => *local,
            _ => return
        };

        match self.mir.local_decls[local].ty.sty {
            TypeVariants::TyRef(_, _, _) => {}
            _ =>
                // The function call doesn't return a reference, so the return place won't store a
                // loan.
                return
        }

        let loans = self.loans_at(location);
        let lhs_loan = loans[0];

        self.set_loans_at_place(block, destination_place, lhs_loan);
    }

}

fn loans_at(
    interner: &Interner,
    borrow_regions: &[(facts::Region, facts::Loan, facts::PointIndex)],
    location: mir::Location
) -> Vec<facts::Loan> {
    let point = Point { location, typ: PointType::Mid };
    let point = interner.get_point_index(&point);
    borrow_regions.iter()
        .filter_map(|(_, l, p)|
            if point == *p {
                Some(*l)
            } else {
                None
            })
        .collect()
}

fn fixpoint_place_to_loans<'tcx>(
    mir: &Mir<'tcx>,
    cfg: &Cfg,
    place_to_loans: HashMap<BasicBlock, HashMap<Place<'tcx>, HashSet<facts::Loan>>>
) -> HashMap<BasicBlock, HashMap<Place<'tcx>, HashSet<facts::Loan>>> {
    let mut fixpoint_place_to_loans = HashMap::new();
    for block in mir.basic_blocks().indices() {
        let mut visited = vec![false; mir.basic_blocks().len()];
        let mut state = HashMap::<Place<'tcx>, HashSet<facts::Loan>>::new();
        cfg.visit_predecessors(&mut visited, block, &mut state, |block, state| {
            if let Some(ptl) = place_to_loans.get(&block) {
                merge_place_to_loans(state, ptl);
            }
        });
        fixpoint_place_to_loans.insert(block, state);
    }
    fixpoint_place_to_loans
}

fn merge_place_to_loans<'a, 'tcx: 'a>(
    left: &'a mut HashMap<Place<'tcx>, HashSet<facts::Loan>>,
    right: &'a HashMap<Place<'tcx>, HashSet<facts::Loan>>
) {
    for (place, loans) in right {
        let loans_entry = left.entry(place.clone()).or_default();
        for loan in loans {
            loans_entry.insert(*loan);
        }
    }
}

fn get_ref_args<'a, 'tcx: 'a>(mir: &Mir<'tcx>, args: &'a [Operand<'tcx>]) -> Vec<&'a Place<'tcx>> {
    let args = args.iter()
        .filter_map(|arg| match arg {
            Operand::Move(place) => Some(place),
            _ => None
        })
        .collect::<Vec<_>>();

    args.into_iter()
        .filter(|arg| match arg {
            Place::Local(local) =>
                match mir.local_decls[*local].ty.sty {
                    TypeVariants::TyRef(_, _, _) => true,
                    _ => false
                }
            _ => unreachable!()
        })
        .collect::<Vec<_>>()
}

struct Cfg {
    predecessors: HashMap<BasicBlock, Vec<BasicBlock>>,
}

impl Cfg {

    fn new(mir: &Mir) -> Self {
        let mut cfg = Cfg { predecessors: HashMap::new() };
        for source in mir.basic_blocks().indices() {
            cfg.predecessors.entry(source).or_default();
            for target in mir[source].terminator().successors() {
                cfg.predecessors.entry(*target).or_default().push(source);
            }
        }
        cfg
    }

    fn predecessors(&self, block: BasicBlock) -> &[BasicBlock] {
        self.predecessors.get(&block)
            .map(|ps| ps as &[BasicBlock])
            .unwrap_or(EMTPY_BASIC_BLOCKS)
    }

    fn visit_predecessors<State>(&self,
        visited: &mut [bool],
        block: BasicBlock,
        state: &mut State,
        operation: impl Fn(BasicBlock, &mut State) + Copy
    ) {
        if !visited[block.index()] {
            visited[block.index()] = true;
            for predecessor in self.predecessors(block).to_vec() {
                self.visit_predecessors(visited, predecessor, state, operation);
            }
            operation(block, state);
        }
    }

}
