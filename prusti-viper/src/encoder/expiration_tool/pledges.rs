use std::collections::HashMap;
use std::collections::HashSet;
use std::str::FromStr;

use itertools::Itertools;

use prusti_interface::environment::mir_utils::AsPlace;
use prusti_interface::environment::mir_utils::PlaceAddProjection;
use prusti_interface::specs::typed;
use prusti_interface::specs::typed::Spanned;
use prusti_specs::specifications::common::AssertionKind;
use rustc_hir::ExprKind;
use rustc_hir::QPath;
use rustc_middle::hir;
use rustc_middle::mir;
use rustc_middle::ty;
use rustc_span::Span;
use rustc_span::symbol::Symbol;

use crate::encoder::errors::EncodingError;
use crate::encoder::places;
use crate::encoder::places::Place;
use crate::encoder::procedure_encoder::Result;
use crate::encoder::reborrow_signature::ReborrowSignature;

use super::Context;

pub(super) type PledgeWithDependencies<'tcx> = (
    typed::Assertion<'tcx>,
    HashSet<PledgeDependency<'tcx>>
);

/// Pledges have dependencies in the sense that some inputs must have been unblocked and some
/// outputs must have expired by the time the pledge is included in a magic wand. This struct
/// captures a single such dependency.
///
/// This is best explained by example. Assume a pledge contains a subexpression
/// ```ignore
/// after_unblocked(p.x) == before_expiry(*result.0)
/// ```
/// This would generate the following `PledgeDependency` for the `after_unblocked` subexpression:
/// ```ignore
/// PledgeDependency {
///   context: AfterUnblocked,
///   place: *p
/// }
/// ```
/// And the following `PledgeDependency` for the `before_expiry` subexpression:
/// ```ignore
/// PledgeDependency {
///   context: BeforeExpiry,
///   place: *result.0
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct PledgeDependency<'tcx> {
    pub(super) context: Context,
    pub(super) place: places::Place<'tcx>,
    span: Span
}

impl<'tcx> PledgeDependency<'tcx> {
    /// Returns
    ///  - `Some(false)` if this dependency is not satisfied.
    ///  - `Some(true)` if this dependency is satisfied now, but wasn't before.
    ///  - `None` if this dependency is satisfied and was satisfied before.
    ///
    /// Here, "before" means before the references from `expired` did expire and the references
    /// from `unblocked` were unblocked.
    pub(super) fn is_satisfied(&self,
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

pub(super) trait PledgeDependenciesSatisfied<'tcx> {
    /// Figures out if the pledge dependencies are newly satisfied, i.e., they are satisfied now
    /// but weren't satisfied before the places from `expired` did expire.
    fn are_newly_satisfied(self,
        blocking: &HashSet<places::Place<'tcx>>,
        blocked: &HashSet<places::Place<'tcx>>,
        expired: &HashSet<places::Place<'tcx>>,
        unblocked: &HashSet<places::Place<'tcx>>,
    ) -> bool;
}

impl<'a, 'tcx: 'a, DS> PledgeDependenciesSatisfied<'tcx> for DS
where DS: IntoIterator<Item=&'a PledgeDependency<'tcx>> {
    fn are_newly_satisfied(self,
        blocking: &HashSet<Place<'tcx>>,
        blocked: &HashSet<Place<'tcx>>,
        expired: &HashSet<Place<'tcx>>,
        unblocked: &HashSet<Place<'tcx>>,
    ) -> bool {
        let (some_transitioned, all_satisfied) = self.into_iter()
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
/// environment and input places that appear inside an `after_unblocked` environment. The result
/// is a list of `PledgeDependency` structs, each of which describes one `before_expiry` or
/// `after_unblocked` instance.
pub(super) fn identify_dependencies<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    mir: &mir::Body<'tcx>,
    reborrow_signature: &ReborrowSignature<places::Place<'tcx>>,
    assertion: &typed::Assertion<'tcx>
) -> Result<HashSet<PledgeDependency<'tcx>>> {
    // Construct a mapping from places to their names in the original program.
    let local_names = mir.var_debug_info.iter()
        .filter_map(|vdi| Some((vdi.place.as_local()?, vdi.name)))
        .collect::<HashMap<_, _>>();

    // Gather all MIR arguments that are references together with their original name name in the
    // source program.
    let inputs = mir.local_decls.indices()
        .skip(1).take(mir.arg_count)
        .map(|local| {
            let name = local_names[&local];
            let place = local.as_place().deref(tcx);
            (name, place)
        })
        .filter(|(_, place)| {
            let place = places::Place::NormalPlace(place.clone());
            reborrow_signature.blocked.contains(&place)
        })
        .collect::<HashMap<_, _>>();

    // Gather all outputs that are references.
    let outputs = reborrow_signature.blocking.iter()
        .map(|place| match place {
            places::Place::NormalPlace(place) => place.clone(),
            _ => unimplemented!() // TODO
        })
        .collect();

    let identifier = DependencyIdentifier { tcx, inputs: &inputs, outputs: &outputs };
    identifier.analyze_assertion(assertion)
}

struct DependencyIdentifier<'v, 'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    inputs: &'v HashMap<Symbol, mir::Place<'tcx>>,
    outputs: &'v HashSet<mir::Place<'tcx>>,
}

impl<'v, 'tcx> DependencyIdentifier<'v, 'tcx> {
    /// See documentation of [identify_dependencies](fn.identify_dependencies.html).
    fn analyze_assertion(&self,
        assertion: &typed::Assertion<'tcx>,
    ) -> Result<HashSet<PledgeDependency<'tcx>>> {
        Ok(match assertion.kind.as_ref() {
            AssertionKind::Expr(expression) =>
                self.analyze_expression(
                    &extract_expression(self.tcx.hir(), expression), None)?,
            AssertionKind::And(assertions) =>
                assertions.iter()
                    .map(|assertion| self.analyze_assertion(assertion))
                    .collect::<Result<Vec<_>>>()?.into_iter().flatten().collect(),
            AssertionKind::Implies(antecedent, consequent) =>
                std::iter::empty()
                    .chain(self.analyze_assertion(antecedent)?)
                    .chain(self.analyze_assertion(consequent)?)
                    .collect(),
            _ => Err(err_unsupported_assertion(assertion, assertion.get_spans(self.tcx)))?
        })
    }

    /// See documentation of [identify_dependencies](fn.identify_dependencies.html).
    fn analyze_expression(&self,
        expression: &rustc_hir::Expr,
        context: Option<Context>
    ) -> Result<HashSet<PledgeDependency<'tcx>>> {
        let before_expiry_dependencies = self.determine_before_expiry_dependencies(expression);
        let after_unblocked_dependencies = self.determine_after_unblocked_dependencies(expression);

        if let Some(context) = context {
            if context == Context::AfterUnblocked && !before_expiry_dependencies.is_empty() {
                Err(err_after_unblocked_contains_outputs(expression))?;
            }
            if context == Context::BeforeExpiry && !after_unblocked_dependencies.is_empty() {
                Err(err_before_expiry_contains_inputs(expression))?;
            }
        }

        let recursive_dependencies = match &expression.kind {
            ExprKind::Binary(_, left, right) =>
                [left, right].iter()
                    .map(|expression| self.analyze_expression(expression, context))
                    .collect::<Result<Vec<_>>>()?.into_iter().flatten().collect(),
            ExprKind::Unary(_, expression) =>
                self.analyze_expression(expression, context)?,
            ExprKind::Call(function, arguments) => {
                let function_name = fully_qualified_name(&function);
                let new_context = update_context(context, &function_name, expression)?;
                let dependencies = arguments.iter()
                    .map(|argument| self.analyze_expression(argument, new_context))
                    .collect::<Result<Vec<_>>>()?.into_iter().flatten().collect::<HashSet<_>>();
                if let Some(new_context) = new_context {
                    if context == None {
                        // We just entered a before_expiry or after_unblocked context, so we
                        // check if it contains the right number of dependencies (i.e., exactly
                        // one).
                        if dependencies.is_empty() {
                            // A before_expiry or after_unblocked context cannot contain no
                            // dependencies.
                            Err(err_ctxt_no_dependencies(new_context, expression))
                        } else if dependencies.len() > 1 {
                            // A before_expiry or after_unblocked context cannot contain multiple
                            // dependencies.
                            Err(err_ctxt_multiple_dependencies(new_context, &dependencies))
                        } else { Ok(dependencies) }
                    } else { Ok(dependencies) }
                } else { Ok(dependencies) }?
            }
            ExprKind::Field(base, _) =>
                self.analyze_expression(base, context)?,
            ExprKind::Block(block, _) => {
                assert!(block.stmts.is_empty());
                let expression = block.expr.as_ref().unwrap();
                self.analyze_expression(expression, context)?
            }
            ExprKind::Path(_) => HashSet::new(),
            ExprKind::Lit(_) => HashSet::new(),
            _ => Err(err_unsupported_expression(expression))?
        };

        let dependencies = std::iter::empty()
            .chain(before_expiry_dependencies)
            .chain(after_unblocked_dependencies)
            .chain(recursive_dependencies)
            .collect();

        Ok(dependencies)
    }

    /// Returns all pledge dependencies on output references that are immediately implied by this
    /// expression, by checking which output references match this expression.
    fn determine_before_expiry_dependencies(&self,
        expression: &rustc_hir::Expr
    ) -> HashSet<PledgeDependency<'tcx>> {
        self.outputs.iter().filter_map(|output| {
            if expr_matches_place(&expression, &output.truncate(self.tcx, 1)) {
                Some(PledgeDependency {
                    context: Context::BeforeExpiry,
                    place: output.clone().into(),
                    span: expression.span
                })
            } else { None }
        }).collect()
    }

    /// Returns all pledge dependencies on input references that are immediately implied by this
    /// expression, by checking which input references match this expression.
    fn determine_after_unblocked_dependencies(&self,
        expression: &rustc_hir::Expr
    ) -> HashSet<PledgeDependency<'tcx>> {
        if let ExprKind::Path(QPath::Resolved(_, path)) = &expression.kind {
            let segments = &path.segments;
            if segments.len() == 1 {
                let name = segments[0].ident.name;
                if let Some(place) = self.inputs.get(&name) {
                    std::iter::once(PledgeDependency {
                        context: Context::AfterUnblocked,
                        place: place.clone().into(),
                        span: expression.span
                    }).collect()
                } else { HashSet::new() }
            } else { HashSet::new() }
        } else { HashSet::new() }
    }
}

/// Given a `typed::Expression`, this method utters some incantations to conjure up the HIR
/// expression representing this `typed::Expression`.
fn extract_expression<'hir>(
    hir: hir::map::Map<'hir>,
    expression: &typed::Expression
) -> &'hir rustc_hir::Expr<'hir> {
    // This is the id of the closure that contains the expression.
    let hir_id = hir.local_def_id_to_hir_id(expression.expr);

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

/// Returns true if the given HIR expression corresponds to the given MIR place. This is not
/// complete by far. The expression and place must be a series of field projections. They must
/// also be based on the return place (i.e., `result` for the HIR expression and `_0` for the MIR
/// place).
fn expr_matches_place<'tcx>(expr: &rustc_hir::Expr, place: &mir::Place<'tcx>) -> bool {
    // We only support the return place.
    if place.local.index() != 0 {
        return false;
    }

    // Turn the expression into a variable and path of fields accessed starting from this variable.
    let (variable, path) = if let Some(result) = expr_to_variable_and_path(expr) {
        result
    } else {
        // The expression is not of a shape that we support.
        return false;
    };

    // We only support the return place.
    if variable.as_str() != "result" {
        return false;
    }

    // If they don't access the same number of fields, they cannot denote the same place.
    if path.len() != place.projection.len() {
        return false;
    }

    // Now that we know that both the HIR expression and the MIR place start at the return place
    // and access the same number of fields, check that they also agree in the list of fields
    // they access.
    place.projection.iter().zip(path.iter()).all(|(place_elem, path_elem)|
        if let mir::ProjectionElem::Field(field, _) = place_elem {
            usize::from_str(&path_elem.as_str()) == Ok(field.index())
        } else {
            // We only support field projections.
            false
        })
}

/// Converts an expression of the form `variable.field1.field2.field3` into the list of symbols
/// [`identifier`, `field1`, `field2`, `field3`].
///
/// If the expression is not of this form, it returns `None`.
fn expr_to_variable_and_path(expr: &rustc_hir::Expr) -> Option<(Symbol, Vec<Symbol>)> {
    match &expr.kind {
        ExprKind::Field(base, ident) => {
            let (variable, mut base_path) = expr_to_variable_and_path(base)?;
            base_path.push(ident.name);
            Some((variable, base_path))
        }
        ExprKind::Path(QPath::Resolved(_, path)) => {
            let segments = &path.segments;
            if segments.len() == 1 {
                Some((segments[0].ident.name, Vec::new()))
            } else { None }
        }
        _ => None
    }
}

/// If this expression is a path like `seg1::seg2::seg3`, it returns the string representation of
/// it. If this expression is not a path, it panics.
fn fully_qualified_name(function: &rustc_hir::Expr) -> String {
    match &function.kind {
        ExprKind::Path(QPath::Resolved(_, path)) =>
            path.segments.iter()
                .map(|segment| segment.ident.name.to_string())
                .join("::"),
        _ => unreachable!()
    }
}

/// A function call can change the context for the argument expressions, if the function called
/// is the the special before_expiry or after_unblocked environment. This function implements
/// this logic based on the name of the called function. It fails if the called function is one
/// of the two special environments and the current context is not `None`, because this would
/// mean a before_expiry or after_unblocked environment is nested inside another before_expiry or
/// after_unblocked environment, which is illegal.
fn update_context(
    current_context: Option<Context>,
    function_name: &str,
    expression: &rustc_hir::Expr
) -> Result<Option<Context>> {
    Ok(match function_name {
        "before_expiry" => {
            assert_context_is_none(&current_context, expression)?;
            Some(Context::BeforeExpiry)
        },
        "after_unblocked" => {
            assert_context_is_none(&current_context, expression)?;
            Some(Context::AfterUnblocked)
        },
        _ => current_context
    })
}

fn assert_context_is_none(
    context: &Option<Context>,
    expression: &rustc_hir::Expr
) -> Result<()> {
    if context.is_some() { Err(err_nested_environments(expression)) }
    else { Ok(()) }
}

fn err_unsupported_assertion(
    assertion: &typed::Assertion,
    spans: Vec<Span>
) -> EncodingError {
    let message = format!("assertions of type {:?} are not supported in pledges yet.",
        assertion.kind);
    EncodingError::incorrect(message, spans)
}

fn err_unsupported_expression(expression: &rustc_hir::Expr) -> EncodingError {
    let message = format!("expressions of type {:?} are not supported in pledges yet.",
        expression.kind);
    EncodingError::incorrect(message, expression.span)
}

fn err_before_expiry_contains_inputs(expression: &rustc_hir::Expr) -> EncodingError {
    let message = "the before_expiry environment cannot contain input references";
    EncodingError::incorrect(message, expression.span)
}

fn err_after_unblocked_contains_outputs(expression: &rustc_hir::Expr) -> EncodingError {
    let message = "the after_unblocked environment cannot contain output references";
    EncodingError::incorrect(message, expression.span)
}

fn err_ctxt_no_dependencies(context: Context, expression: &rustc_hir::Expr) -> EncodingError {
    let message = format!(
        "this {} environment must contain at least one input or output reference",
        context);
    EncodingError::incorrect(message, expression.span)
}

fn err_ctxt_multiple_dependencies(
    context: Context,
    dependencies: &HashSet<PledgeDependency>
) -> EncodingError {
    let spans = dependencies.iter().map(|pd| pd.span).collect::<Vec<_>>();
    let message = format!(
        "this {} environment has dependencies on multiple inputs or outputs ",
        context);
    EncodingError::incorrect(message, spans)
}

fn err_nested_environments(expression: &rustc_hir::Expr) -> EncodingError {
    let message = "cannot nest a before_expiry or after_unblocked environment inside another \
        before_expiry or after_unblocked environment.";
    EncodingError::incorrect(message, expression.span)
}
