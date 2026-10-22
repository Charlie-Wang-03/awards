# JSP-000404 — Lean repairs and residual-chain checkpoint (2026-10-22)

Research branch: `research/jsp-000404-sharp-centre`.
Scope: partial mathematical formalization; **not** a complete proof or disproof of the original problem.

## Three focused kernel-verified repairs

1. `JSP000404Research/ConcreteSecondDeletionRigidity.lean`
   - Repaired exact parent-to-child exponent transport in `no_concrete_secondDeletion_unit_gain_above_min`.
   - Repaired the dependent `pre,post,hsplit` pattern-match normalization in `second_minimum_deleted_ray_adjacent_zero_at_high_survivor`.
   - Successful focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/39729987519
   - Build: 3522 jobs; audited declarations show standard axioms and no `sorryAx`.

2. `JSP000404Research/CutCentreTransitionRefinement.lean`
   - Moved the `lam` binder before `AngleCap p lam` to avoid Lean auto-implicit shadowing.
   - Replaced implicit index simplification by the verified equivalence inverses `rayIndex_get` and `get_rayIndex`.
   - Made predecessor subtraction arithmetic explicit, and constructed the minimum changed-sign membership witness by `Finset.mem_filter.mpr`.
   - Recovered adjacent transition and normalized angle-gap inequalities, without adding a geometric assumption.
   - Successful focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/39730567583
   - Build: 8960 jobs; two theorem axiom reports are `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

3. `JSP000404Research/SixPointSupportThreeShape.lean`
   - Removed an already-closed `norm_num` step and repaired the nested list-case proof.
   - Moved the `lam` binder before `AngleCap p lam`.
   - Recovered the sharp-pinned six-point support-three terminal: a middle length-three quotient list with exactly one positive value has shape `[q,0,0]`, `[0,q,0]` or `[0,0,q]`, for `q ≠ 0`.
   - Successful focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/39730467941
   - Build: 3532 jobs. Axioms:
     - `centreRayList_length_eq_card_sub_one`: `[propext, Classical.choice, Quot.sound]`
     - `length_three_positiveCount_one_shape`: `[propext, Quot.sound]`
     - `exists_six_point_sharp_pinned_support_three_shape`: `[propext, Classical.choice, Quot.sound]`
     No `sorryAx` for these declarations.

Focused workflows added:
- `.github/workflows/jsp000404-focused-concrete-second-deletion-rigidity.yml`
- `.github/workflows/jsp000404-focused-cut-centre-transition-refinement.yml`
- `.github/workflows/jsp000404-focused-six-point-support-three-shape.yml`

## Exact remaining mathematical obligations

The root `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` retains exactly one intentional `sorry` (near line 900), and its headline axiom audit still includes `sorryAx`. This has **not** been removed, retyped as an unproved hypothesis, or represented as closed.

Verified planar low-parameter branches `n=1`, `n=2`, and at most four original centres are distinct from the unresolved all-cardinality regime `n>=3`, original centres `>=5`.

For the genuine `n=3`, five-centre slice, existing source-backed Lean lemmas reduce dyadic mass violation to:
- no exponent-two centre, at least four exponent-one centres; or
- one exponent-two centre and exactly one exponent-one centre.

Neither motif has been excluded from genuine `AngleCap` geometry. The repaired six-point support-three terminal is a further finite case reduction, **not** a geometric exclusion or a global compensation theorem.

The general proof gap remains the original-vertex-level globally non-reusing six-source payment, compatible with real TRUE Boolean holes, dyadic surplus, covered loss, soft/rigid/mixed sources and NET duplicate debt. A coloured-slot matching alone does not satisfy this obligation.

## Build boundaries

A focused `lake build <module>` success means that the module and its imported dependencies compile. It does not certify `JSP000404Research` as a whole or settle the published-source validity gate. The historical fast-incremental all-modules workflow previously reported 169 explicit Lean error entries across 15 files, including cascading errors; a fresh successful full build is required to update the whole-tree status.

No upstream complete-proof submission or priority claim is implied by this checkpoint.
