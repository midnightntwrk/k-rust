//! Mutation switches for the verification of the check (the design's V7): each turns one rule of
//! the check, the closure or the gate off, so that a test can show the oracle test meant to catch
//! that class fails without it. Outside test builds every switch is off and [`active`] is a
//! constant, so the checks that read it compile away.

/// The switches; all off by default.
#[derive(Clone, Copy, Debug, Default)]
#[allow(
    clippy::struct_excessive_bools,
    reason = "independent test-only mutation flags"
)]
#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "the definition reads two switches in test builds only"
    )
)]
pub(crate) struct Switches {
    /// Enumerate root pairs only.
    pub(crate) drop_inner_positions: bool,
    /// Unify two sorts' variables only at their common sort, never at maximal common subsorts.
    pub(crate) drop_glb_branches: bool,
    /// Unify without the overload axioms.
    pub(crate) drop_lifting: bool,
    /// Bind a variable against a greater application only to that application.
    pub(crate) drop_lesser_productions: bool,
    /// Pair an inner position only with equations of the outer equation's priority.
    pub(crate) separate_inner_by_priority: bool,
    /// Call every conditional overlap refuted.
    pub(crate) refute_every_condition: bool,
    /// Do not compare the two equations' `ensures`.
    pub(crate) ignore_ensures: bool,
    /// Let the join take a step that erases a residual not shown defined.
    pub(crate) erase_partial_residuals: bool,
    /// Let the join step past a redex it refused.
    pub(crate) decompose_refused_redex: bool,
    /// Let the join apply an equation without refuting the higher priority groups.
    pub(crate) ignore_higher_groups: bool,
    /// Offer the join `symbolic` equations as steps.
    pub(crate) join_with_symbolic: bool,
    /// Do not rename the second equation apart from the first.
    pub(crate) no_rename_apart: bool,
    /// Run the check with every claim admitted.
    pub(crate) claims_during_check: bool,
    /// Discharge the rewrite rules' definedness with every claim admitted, before the check.
    pub(crate) discharge_before_check: bool,
    /// Closure: no T1.
    pub(crate) drop_t1: bool,
    /// Closure: T-sym ignores right-hand sides.
    pub(crate) drop_tsym_rhs: bool,
    /// Closure: no T-obs.
    pub(crate) drop_tobs: bool,
    /// Closure: T0 taints the pairs' root symbols only, not their equations.
    pub(crate) seed_heads_only: bool,
    /// Gate: admit every index at the scan's equation-head arm.
    pub(crate) admit_equation_heads: bool,
    /// Gate: admit every index at the certificate.
    pub(crate) admit_certificates: bool,
    /// Normal-form sorts: no supersort closure (an overlap whose variable's sort gets its
    /// elements only from a subsort is called vacuous).
    pub(crate) drop_supersort_inhabitation: bool,
    /// Join: read every function application as never a normal form, and a stuck one as
    /// `\bottom` (revision 2's 3.13 (c) before R1.5).
    pub(crate) stuck_total_is_bottom: bool,
    /// `SortReach`: collapse every non-injective total symbol and every uninterpreted symbol,
    /// whether or not its sort is surely inhabited (revision 2's 3.13 (l) before R1.3).
    pub(crate) collapse_every_total: bool,
    /// Conditions: read `a <=Int b` as `notBool (a <Int b)` instead of `notBool (b <Int a)`.
    pub(crate) misread_int_le: bool,
    /// Never pair an equation with itself at the root (before the revision after review 2).
    pub(crate) drop_several_matches: bool,
    /// `SortReach`: no edges from a collection sort to its element, key and value sorts.
    pub(crate) drop_collection_edges: bool,
    /// Drop every inner pair whose second equation has a sort below the position's (review 2's
    /// seeded defect D9).
    pub(crate) drop_injected_inner: bool,
    /// Self pairs: read only the right-hand side, not the `ensures` (review 3's seed S1).
    pub(crate) self_pair_ignores_ensures: bool,
    /// Self pairs: read a right-hand side the check does not read (a disjunction, `\top`,
    /// predicates) as reading no variable (review 3's seed S5).
    pub(crate) self_pair_reads_opaque_rhs_as_nothing: bool,
}

#[cfg(test)]
thread_local! {
    static ACTIVE: std::cell::Cell<Switches> = const {
        std::cell::Cell::new(Switches {
            drop_inner_positions: false,
            drop_glb_branches: false,
            drop_lifting: false,
            drop_lesser_productions: false,
            separate_inner_by_priority: false,
            refute_every_condition: false,
            ignore_ensures: false,
            erase_partial_residuals: false,
            decompose_refused_redex: false,
            ignore_higher_groups: false,
            join_with_symbolic: false,
            no_rename_apart: false,
            claims_during_check: false,
            discharge_before_check: false,
            drop_t1: false,
            drop_tsym_rhs: false,
            drop_tobs: false,
            seed_heads_only: false,
            admit_equation_heads: false,
            admit_certificates: false,
            drop_supersort_inhabitation: false,
            stuck_total_is_bottom: false,
            collapse_every_total: false,
            misread_int_le: false,
            drop_several_matches: false,
            drop_collection_edges: false,
            drop_injected_inner: false,
            self_pair_ignores_ensures: false,
            self_pair_reads_opaque_rhs_as_nothing: false,
        })
    };
}

/// The switches in force on this thread.
#[inline]
pub(crate) fn active() -> Switches {
    #[cfg(test)]
    {
        ACTIVE.get()
    }
    #[cfg(not(test))]
    {
        Switches::default()
    }
}

/// Runs `run` with `switches` in force on this thread.
#[cfg(test)]
pub(crate) fn with<R>(switches: Switches, run: impl FnOnce() -> R) -> R {
    let previous = ACTIVE.replace(switches);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(run));
    ACTIVE.set(previous);
    result.unwrap_or_else(|panic| std::panic::resume_unwind(panic))
}
