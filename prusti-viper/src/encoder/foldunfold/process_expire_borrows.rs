#![warn(warnings)]

use std::collections::HashMap;
use std::ops::Deref;

use itertools::Itertools;
use log::*;

use prusti_common::vir;
use prusti_common::vir::CfgReplacer;

use crate::utils::unionfind::find;
use crate::utils::unionfind::union;

use super::action::Action;
use super::FoldUnfold;
use super::FoldUnfoldError;
use super::path_ctxt::PathCtxt;

impl<'p, 'v: 'p, 'tcx: 'v> FoldUnfold<'p, 'v, 'tcx> {
    /// Generates Viper statements that expire all the borrows from the given `dag`. The
    /// `surrounding_pctxt` will be modified to reflect the path context after the borrows have
    /// been expired.
    pub(super) fn process_expire_borrows(
        &mut self,
        dag: &vir::borrows::DAG,
        pctxt: PathCtxt<'p>,
        bb_index: vir::CfgBlockIndex,
        new_cfg: &vir::CfgMethod,
        label: Option<&str>,
    ) -> Result<(PathCtxt<'p>, Vec<vir::Stmt>), FoldUnfoldError> {
        trace!("[enter] process_expire_borrows dag=[{:?}]", dag);

        // Identify the connected component for every loan.
        let mut representatives = HashMap::new();
        for node in dag.iter() {
            for &in_borrow in &node.reborrowing_nodes {
                union(&mut representatives, &[node.borrow, in_borrow]);
            }
        }

        // Identify the roots of the re-borrowing graph, which are the nodes that don't re-borrow
        // from anyone.
        let roots = dag.iter()
            .filter(|node| node.reborrowed_nodes.is_empty())
            .collect::<Vec<_>>();
        assert!(!roots.is_empty());

        // Group the roots by their connected component.
        let root_groups: Vec<Vec<&vir::borrows::Node>> = roots.into_iter()
            .sorted_by_key(|leaf| find(&representatives, leaf.borrow))
            .group_by(|leaf| find(&representatives, leaf.borrow)).into_iter()
            .map(|(_, items)| items.into_iter().collect::<Vec<_>>())
            .collect::<Vec<_>>();

        // Process all the root groups sequentially. This means the initial path context for every
        // root group will be the final path context of the preceding root group.
        let (pctxt, stmts) = root_groups.into_iter().try_fold(
            (pctxt.clone(), Vec::new()),
            |(pctxt, stmts), root_group| {
                // Process all the root nodes from this root group in parallel. This means the
                // initial path context for every root node will be the same.
                let (in_pctxts, in_stmts) = self.recurse_incoming_nodes(
                    dag, &pctxt, &root_group, bb_index, new_cfg, label)?;
                let (pctxt, new_stmts) = self.join_incoming_nodes(
                    dag, &root_group, &in_pctxts, in_stmts)?;
                let stmts = [&stmts[..], &new_stmts[..]].concat();
                Ok((pctxt, stmts))
            })?;

        Ok((pctxt, stmts))
    }

    fn recurse_incoming_nodes(&mut self,
        dag: &vir::borrows::DAG,
        initial_pctxt: &PathCtxt<'p>,
        incoming_nodes: &Vec<&vir::borrows::Node>,
        /* junk */
        bb_index: vir::CfgBlockIndex,
        new_cfg: &vir::CfgMethod,
        label: Option<&str>,
    ) -> Result<(Vec<PathCtxt<'p>>, Vec<Vec<vir::Stmt>>), FoldUnfoldError> {
        let result = incoming_nodes.iter()
            .map(|incoming_node| self.process_node(
                dag, incoming_node, initial_pctxt, bb_index, new_cfg, label))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter().unzip();
        Ok(result)
    }

    fn join_incoming_nodes(&mut self,
        dag: &vir::borrows::DAG,
        incoming_nodes: &[&vir::borrows::Node],
        incoming_pctxts: &[PathCtxt<'p>],
        mut incoming_stmts: Vec<Vec<vir::Stmt>>
    ) -> Result<(PathCtxt<'p>, Vec<vir::Stmt>), FoldUnfoldError> {
        let (actions, mut pctxt) = self.prepend_join(incoming_pctxts.iter().collect())?;
        for (i, actions) in actions.iter().enumerate() {
            for action in actions.deref() {
                incoming_stmts[i].push(action.to_stmt());
                if let Action::Drop(perm, missing_perm) = action {
                    let condition_a = dag.in_borrowed_places(missing_perm.get_place());
                    let condition_b = perm.get_perm_amount() != vir::PermAmount::Read;
                    if condition_a && condition_b {
                        pctxt.mut_state().restore_dropped_perm(perm.clone());
                    }
                }
            }
        }

        let stmts = incoming_stmts.into_iter().enumerate().fold(
            Vec::new(),
            |elze, (i, then)| {
                let guard = incoming_nodes[i].guard.clone();
                vec![vir::Stmt::If(guard, then, elze)]
            });

        Ok((pctxt, stmts))
    }

    fn process_node(
        &mut self,
        dag: &vir::borrows::DAG,
        node: &vir::borrows::Node,
        initial_pctxt: &PathCtxt<'p>,
        /* junk */
        bb_index: vir::CfgBlockIndex,
        new_cfg: &vir::CfgMethod,
        label: Option<&str>,
    ) -> Result<(PathCtxt<'p>, Vec<vir::Stmt>), FoldUnfoldError> {
        let incoming_nodes = node.reborrowing_nodes.iter()
            .map(|&borrow| dag.node_for_borrow(borrow))
            .collect::<Vec<_>>();

        let (mut pctxt, mut stmts) = if incoming_nodes.is_empty() {
            (initial_pctxt.clone(), Vec::new())
        } else {
            let (mut incoming_pctxts, incoming_stmts) = self.recurse_incoming_nodes(
                dag, initial_pctxt, &incoming_nodes, bb_index, new_cfg, label)?;

            // restore dropped permissions.
            let incoming_nodes_with_pctxt = incoming_nodes.iter().zip(incoming_pctxts.iter_mut());
            for (incoming_node, incoming_pctxt) in incoming_nodes_with_pctxt {
                let end_block = self.get_cfg_block_of_last_borrow(bb_index, &incoming_node.borrow);
                let start_block = self.get_cfg_block_of_last_borrow(bb_index, &node.borrow);
                if start_block != end_block {
                    let path = new_cfg.find_path(start_block, end_block).unwrap();
                    let dropped_perms = initial_pctxt.log().collect_dropped_permissions(&path, dag);
                    incoming_pctxt.mut_state().restore_dropped_perms(dropped_perms.into_iter());
                }
            }

            self.join_incoming_nodes(dag, &incoming_nodes, &incoming_pctxts, incoming_stmts)?
        };

        stmts.push(vir!(# format!("expiring loan {:?}", node.borrow)));

        for (stmt_index, stmt) in node.stmts.iter().enumerate() {
            stmts.extend(self.replace_stmt(
                stmt_index, stmt, false, &mut pctxt, bb_index, new_cfg, label
            )?);
        }

        // Remove read permissions.
        let duplicated_perms = initial_pctxt.log().get_duplicated_read_permissions(node.borrow);
        let mut maybe_original_place = None;
        for (mut read_access, original_place) in duplicated_perms {
            if let Some(ref place) = node.place {
                read_access = read_access.replace_place(&original_place, place);
            }
            maybe_original_place = Some(original_place);
            let stmt = vir::Stmt::Exhale(read_access, self.method_pos);
            stmts.extend(self.replace_stmt(
                stmts.len(), &stmt, false, &mut pctxt,
                bb_index, new_cfg, label
            )?);
        }
        if let Some(original_place) = maybe_original_place {
            if pctxt.state().contains_acc(&original_place) {
                pctxt.mut_state().insert_moved(original_place);
            }
        }

        // Restore write permissions.
        // Currently, we have a simplified version that restores write permissions only when
        // all borrows in the conflict set are dead. This is sound, but less complete.
        // TODO: Implement properly so that we can restore write permissions to the prefix only
        // when there is still alive conflicting borrown. For example, when the currently expiring
        // borrow borrowed `x.f`, but we still have a conflicting borrow that borrowed `x.f.g`, we
        // would need to restore write permissions to `x.f` without doing the same for `x.f.g`.
        // This would require making sure that we are unfolded up to `x.f.g` and emit
        // restoration for each place segment separately.
        if node.alive_conflicting_borrows.is_empty() {
            for &borrow in &node.conflicting_borrows {
                stmts.extend(self.restore_write_permissions(borrow, &mut pctxt)?);
            }
            stmts.extend(self.restore_write_permissions(node.borrow, &mut pctxt)?);
        }

        Ok((pctxt, stmts))
    }
}
