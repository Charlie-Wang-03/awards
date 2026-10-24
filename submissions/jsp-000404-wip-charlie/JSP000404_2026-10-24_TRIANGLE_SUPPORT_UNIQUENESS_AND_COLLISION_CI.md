# JSP-000404 — genuine short-triangle certificate uniqueness and Lean repair checkpoint

Date: 2026-10-24. Downstream research branch: `research/jsp-000404-sharp-centre`. Scope is **research-only**. There is **no complete proof or disproof**.

## New sorry-free original-plane statements

1. `SeparatedSupportTwoResidualBudget.separated_support_two_double_zero_middle_angle_budget`: whenever both top-adjacent quotient gaps at a true deficit-three/support-two centre vanish, the middle zero-angle mass is at most `(3*delta-1)*lam`, forcing `delta >= 1/3`. **[CI 40065565121 PASS](https://github.com/Charlie-Wang-03/awards/actions/runs/40065565121)**, 3553 Lake jobs.

2. `SmallTriangleApexUniqueness.actual_small_triangle_apex_unique_of_same_support`: under true original-plane `AngleCap p lam`, `0 < lam` and `delta < 1/2`, two angle certificates no larger than `delta*lam` indexed by the same *unordered three-vertex original-plane Finset* must have the same apex. **[CI 40066690013 PASS](https://github.com/Charlie-Wang-03/awards/actions/runs/40066690013)**, 3554 Lake jobs; `#print axioms` reports `[propext, Classical.choice, Quot.sound]`.

3. `SmallPairHardBranchDistinctSupports.small_pair_away_from_top_distinct_triangle_supports`: for any two different source centres equipped with real `SmallPairAwayFromTop` certificates, their unordered original-three-vertex triangle supports cannot coincide. Thus the actual pure two-minimum six-centre hard branch has a direct nonreuse criterion for its *geometric triangle supports*. **[CI 40067078291 PASS](https://github.com/Charlie-Wang-03/awards/actions/runs/40067078291)**, 9151 Lake jobs; `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`.

**Important distinction:** The results above prevent duplicate charges to the **same original geometric triangle**, but **do not** construct an injective allocation to genuinely uncovered Boolean words, and do not pay any unreserved dyadic debt. They do not imply global dyadic capacity.

## Source-level restoration

The formerly failing five hard branch modules `FiveMinimaColourGraph`, `SixPointOrdinaryInsideBadPalette`, `SixPointHardLowSupportGeometry`, `CutSaturatedSupportMismatch` and `CutMergedRepeatedSmallAngle` all **[PASS focused CI 40065984799](https://github.com/Charlie-Wang-03/awards/actions/runs/40065984799)** (9148 Lake jobs), including explicit relevant axiom audits with no `sorryAx`.

The large `ResidualEnlargedCollisionSimpleGraph.lean` is isolated by `.github/workflows/jsp000404-focused-enlarged-collision-compile.yml`. Its [CI 40066491073](https://github.com/Charlie-Wang-03/awards/actions/runs/40066491073) diagnosed 29 Lean errors; after first repairs, [CI 40066959655](https://github.com/Charlie-Wang-03/awards/actions/runs/40066959655) diagnosed 24 errors. These are **historical, commit-specific measurements**, not claims about the subsequent source. Further patches `7a74a4aa` and `0f276ce1` resolve structural proof indentation, finite sums, residual-edge witnesses, proper-subset/cardinality reasoning and dyadic slack expression order. Latest focused [CI 40067482771](https://github.com/Charlie-Wang-03/awards/actions/runs/40067482771) and full incremental [CI 40067482790](https://github.com/Charlie-Wang-03/awards/actions/runs/40067482790) were still running at this checkpoint; **no PASS is claimed** for their contents.

## Exactly one outstanding genuine proof hole

`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`, theorem `planar_lower_branch_dyadic_capacity_admitted_wip`, still contains the actual global-payment `sorry`. It requires a genuinely active translated-loss choice, nonreusing charge of terminal twin/other-five debt, ACTUAL same-colour retained-edge blocker union and cross-coordinate translated-loss duplication against TRUE holes outside all translated words and genuinely unreserved dyadic surplus.

Conditional inequalities and collision matching reductions elsewhere are **not** global geometric payment. The source-closure gate remains OPEN. Do not silently promote these partial or conditional results as the prize theorem.

No new `sorry`, `admit`, user axiom, or false true-hole credit has been inserted for these results.
