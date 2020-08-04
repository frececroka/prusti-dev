use std::collections::HashMap;
use std::collections::HashSet;
use std::str::FromStr;

use itertools::Itertools;

use prusti_interface::environment::mir_utils::AsPlace;
use prusti_interface::environment::mir_utils::PlaceAddProjection;
use prusti_interface::environment::reborrow_signature::ReborrowSignature;
use prusti_interface::specs::typed;
use rustc_middle::hir;
use rustc_middle::mir;
use rustc_middle::ty;
use rustc_span::symbol::Symbol;

use crate::encoder::places;
use crate::encoder::places::Place;

/// Pledges have dependencies in the sense that some inputs must have been unblocked and some
/// outputs must have expired by the time the pledge is included in a magic wand. This struct
/// captures a single such dependency.
///
/// This is best explained by example. Assume a pledge contains a subexpression
/// ```ignore
/// after_unblocked(p.x)
/// ```
/// This would generate the following `PledgeDependency`:
/// ```ignore
/// PledgeDependency {
///   context: AfterUnblocked,
///   place: *p,
///   expression: <HirId of "p.x">
/// }
/// ```
#[derive(Debug)]
pub struct PledgeDependency<'tcx> {
    pub context: Context,
    pub place: places::Place<'tcx>,
    pub expression: rustc_hir::HirId
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Context { BeforeExpiry, AfterUnblocked }

impl<'tcx> PledgeDependency<'tcx> {
    /// Returns
    ///  - `Some(false)` if this dependency is not satisfied.
    ///  - `Some(true)` if this dependency is satisfied now, but wasn't before.
    ///  - `None` if this dependency is satisfied and was satisfied before.
    ///
    /// Here, "before" means before the references from `expired` did expire and the references
    /// from `unblocked` were unblocked.
    pub fn is_satisfied(&self,
        blocking: &HashSet<Place<'tcx>>,
        blocked: &HashSet<Place<'tcx>>,
        expired: &HashSet<Place<'tcx>>,
        unblocked: &HashSet<Place<'tcx>>,
    ) -> Option<bool> {
        let (transitioned, pending) = match self.context {
            Context::BeforeExpiry => (expired, blocking),
            Context::AfterUnblocked => (unblocked, blocked)
        };
        if transitioned.contains(&self.place) {
            Some(true)
        } else if pending.contains(&self.place) {
            Some(false)
        } else {
            None
        }
    }
}

pub trait PledgeDependenciesSatisfied<'tcx> {
    /// Figures out if the pledge dependencies are newly satisfied, i.e., they are satisfied now
    /// but weren't satisfied before the places from `expired` did expire.
    fn are_newly_satisfied(&self,
        blocking: &HashSet<places::Place<'tcx>>,
        blocked: &HashSet<places::Place<'tcx>>,
        expired: &HashSet<places::Place<'tcx>>,
        unblocked: &HashSet<places::Place<'tcx>>,
    ) -> bool;
}

impl<'tcx, DS> PledgeDependenciesSatisfied<'tcx> for DS
where DS: AsRef<[PledgeDependency<'tcx>]> {
    fn are_newly_satisfied(&self,
        blocking: &HashSet<Place<'tcx>>,
        blocked: &HashSet<Place<'tcx>>,
        expired: &HashSet<Place<'tcx>>,
        unblocked: &HashSet<Place<'tcx>>,
    ) -> bool {
        let (some_transitioned, all_satisfied) = self.as_ref().into_iter()
            .map(|pd| pd.is_satisfied(blocking, blocked, expired, unblocked))
            .fold((false, true), |(some_transitioned, all_satisfied), satisfied| match satisfied {
                Some(state) => (
                    some_transitioned || state,
                    all_satisfied && state
                ),
                None => (some_transitioned, all_satisfied)
            });
        some_transitioned && all_satisfied
    }
}

/// Analyzes the assertion and determines all return places that appear inside a `before_expiry`
/// environment and input places that appear inside an `after_unblocked` environment (first &
/// second tuple element, respectively).
pub fn identify_dependencies<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    mir: &mir::Body<'tcx>,
    reborrow_signature: &ReborrowSignature<places::Place<'tcx>>,
    assertion: &typed::Assertion<'tcx>
) -> Vec<PledgeDependency<'tcx>> {
    let local_names = mir.var_debug_info.iter()
        .filter_map(|vdi|
            if let Some(local) = vdi.place.as_local() {
                Some((local, vdi.name))
            } else {
                None
            }
        )
        .collect::<HashMap<_, _>>();

    let inputs = mir.local_decls.indices()
        .skip(1).take(mir.arg_count)
        .map(|local| {
            let name = local_names[&local];
            let place = local.as_place().deref(tcx);
            (name, place)
        })
        .filter(|(_, place)| {
            let place = places::Place::NormalPlace(place.clone());
            reborrow_signature.inputs.contains(&place)
        })
        .collect::<HashMap<_, _>>();

    let outputs = reborrow_signature.outputs.iter()
        .map(|place| match place {
            places::Place::NormalPlace(place) => place.clone(),
            _ => unimplemented!() // TODO
        })
        .collect();

    let mut dependencies = Vec::new();

    identify_dependencies_of_assertion(
        assertion, tcx.hir(), &inputs, &outputs, &mut dependencies);

    dependencies
}

fn identify_dependencies_of_assertion<'tcx, 'hir>(
    assertion: &typed::Assertion<'tcx>,
    hir: hir::map::Map<'hir>,
    inputs: &HashMap<Symbol, mir::Place<'tcx>>,
    outputs: &HashSet<mir::Place<'tcx>>,
    dependencies: &mut Vec<PledgeDependency<'tcx>>,
) {
    use prusti_specs::specifications::common::AssertionKind::*;
    match assertion.kind.as_ref() {
        Expr(expression) => {
            let expression = extract_expression(hir, expression);
            identify_dependencies_of_expression(
                &expression, inputs, outputs, None, dependencies)
        },
        And(assertions) => {
            for assertion in assertions {
                identify_dependencies_of_assertion(
                    assertion, hir, inputs, outputs, dependencies);
            }
        },
        Implies(antecedent, consequent) => {
            identify_dependencies_of_assertion(
                antecedent, hir, inputs, outputs, dependencies);
            identify_dependencies_of_assertion(
                consequent, hir, inputs, outputs, dependencies);
        }
        _ => unreachable!()
    }
}

fn identify_dependencies_of_expression<'tcx>(
    expression: &rustc_hir::Expr,
    inputs: &HashMap<Symbol, mir::Place<'tcx>>,
    outputs: &HashSet<mir::Place<'tcx>>,
    context: Option<(Context, rustc_hir::HirId)>,
    dependencies: &mut Vec<PledgeDependency<'tcx>>,
) {
    use rustc_hir::ExprKind::*;
    use rustc_hir::QPath;
    match &expression.kind {
        Binary(_, left, right) => {
            identify_dependencies_of_expression(
                left, inputs, outputs, context, dependencies);
            identify_dependencies_of_expression(
                right, inputs, outputs, context, dependencies);
        },
        Unary(_, expression) => {
            identify_dependencies_of_expression(
                expression, inputs, outputs, context, dependencies);
        }
        Call(function, arguments) => {
            let function_name = match &function.kind {
                Path(QPath::Resolved(_, path)) =>
                    path.segments.iter()
                        .map(|segment| segment.ident.name.to_string())
                        .join("::"),
                _ => unreachable!()
            };
            let context = match function_name.as_str() {
                "before_expiry" => {
                    assert!(context.is_none());
                    Some((Context::BeforeExpiry, arguments[0].hir_id))
                },
                "after_unblocked" => {
                    assert!(context.is_none());
                    Some((Context::AfterUnblocked, arguments[0].hir_id))
                },
                _ => context
            };
            for argument in arguments.iter() {
                identify_dependencies_of_expression(
                    argument, inputs, outputs, context, dependencies);
            }
        },
        Field(base, _) => {
            if let Some((Context::BeforeExpiry, dependant_expression)) = context {
                for output in outputs {
                    if expr_matches_place(&expression, output) {
                        dependencies.push(PledgeDependency {
                            context: Context::BeforeExpiry,
                            place: output.clone().into(),
                            expression: dependant_expression
                        });
                    }
                }
            }
            identify_dependencies_of_expression(
                base, inputs, outputs, context, dependencies);
        },
        Path(QPath::Resolved(_, path)) => {
            let segments = &path.segments;
            if segments.len() == 1 {
                if let Some((Context::AfterUnblocked, dependant_expression)) = context {
                    let name = segments[0].ident.name;
                    if let Some(place) = inputs.get(&name) {
                        dependencies.push(PledgeDependency {
                            context: Context::AfterUnblocked,
                            place: place.clone().into(),
                            expression: dependant_expression
                        });
                    }
                }
            }
        },
        Block(block, _) => {
            assert!(block.stmts.is_empty());
            let expression = block.expr.as_ref().unwrap();
            identify_dependencies_of_expression(
                expression, inputs, outputs, context, dependencies);
        }
        _ => unreachable!(),
    }
}

/// Returns true if the given HIR expression corresponds to the given MIR place. This is not
/// complete by far. The expression and place must be a series of field projections. They must
/// also be based on the return place (i.e., `result` for the HIR expression and `_0` for the MIR
/// place).
fn expr_matches_place<'tcx>(expr: &rustc_hir::Expr, place: &mir::Place<'tcx>) -> bool {
    if place.local.index() != 0 {
        // We only support the return place.
        return false;
    }

    let path = if let Some(path) = expr_to_path(expr) {
        path
    } else {
        // The expression is not of a shape that we support.
        return false;
    };

    if path[0].as_str() != "result" {
        // We only support the return place.
        return false;
    }

    for (place_elem, path_elem) in place.projection.iter().zip(path[1..].iter()) {
        if let mir::ProjectionElem::Field(field, _) = place_elem {
            if usize::from_str(&path_elem.as_str()) != Ok(field.index()) {
                return false;
            }
        } else {
            // We only support field projections.
            return false;
        }
    }

    true
}

fn expr_to_path(expr: &rustc_hir::Expr) -> Option<Vec<Symbol>> {
    use rustc_hir::ExprKind::*;
    use rustc_hir::QPath;
    match &expr.kind {
        Field(base, ident) =>
            if let Some(mut base_path) = expr_to_path(base) {
                base_path.push(ident.name);
                Some(base_path)
            } else {
                None
            },
        Path(QPath::Resolved(_, path)) => {
            let segments = &path.segments;
            if segments.len() == 1 {
                Some(vec![segments[0].ident.name])
            } else { None }
        },
        _ => None
    }
}

fn extract_expression<'hir>(
    hir: hir::map::Map<'hir>,
    expression: &typed::Expression
) -> &'hir rustc_hir::Expr<'hir> {
    // This is the id of the closure that contains the expression.
    let hir_id = hir.as_local_hir_id(expression.expr);

    // This is the closure.
    let closure = hir.expect_expr(hir_id);
    let closure_body_id = match &closure.kind {
        rustc_hir::ExprKind::Closure(_, _, body, _, _) => body.hir_id,
        _ => unreachable!()
    };

    // This is the body of the closure
    let body = hir.expect_expr(closure_body_id);
    match &body.kind {
        rustc_hir::ExprKind::Block(block, _) => {
            assert!(block.stmts.is_empty());
            block.expr.unwrap()
        },
        _ => unreachable!()
    }
}
