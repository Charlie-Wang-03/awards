# JSP-000404 — 2026-10-21 exact n=2 sharp gate and arbitrary-cut geometry

Research branch: `research/jsp-000404-sharp-centre`.
**Not a completed proof or disproof.** The global admitted root
`PlanarLowerBranchProofAdmittedWIP.lean` retains its single intentional
`sorry` for real nonreused six-source Boolean-hole/dyadic-surplus payment.
The paper-source validation gate is separately still open.

## Kernel-certified items

1. **Arbitrary projective cut local band budget.**
   `CutProjectiveBandBudget.lean`, successful [CI #39460621335](https://github.com/Charlie-Wang-03/awards/actions/runs/39460621335),
   Lake 8959 jobs, axioms `[propext, Classical.choice, Quot.sound]` (no `sorryAx`):
   - `centreExponent_le_missing_cutProjectiveBands`;
   - `cutProjectiveBandPartition_active_card_le_deficit`.
   This links the actual planar centre exponent to the active colour count
   of an actual *cut-rotated* binary edge partition for every `0 <= c < pi`.
   No external TRUE hole/surplus payment is inferred.

2. **Sharp arithmetic saturation at n=2 / four centres.**
   `PlanarLowerTwoFourSharpObstruction.lean`, successful
   [CI #39461733628](https://github.com/Charlie-Wang-03/awards/actions/runs/39461733628),
   3507 jobs, no `sorryAx`.
   `saturated_dyadic_capacity_iff_all_zero`: for any finite four-labelled
   (or general size `2^n`) dyadic family, capacity `sum 2^e <= 2^n`
   iff every exponent vanishes. Its projected real-geometry specialization
   `planar_lower_branch_n_two_four_capacity_iff_no_top` proves exactly:
   ```text
   n=2, card(ProjectionOrdered V)=4, actual AngleCap and centre cycles:
   (sum_i 2^(centreExponent i) <= 4) ↔
     forall i, centreExponent i != 1
   ```
   Thus eliminating actual exponent-one centres is mathematically NECESSARY
   AND SUFFICIENT to finish the n=2 four-centre branch.

3. **Sharp convex quadrilateral numeric exclusion.**
   `PlanarLowerTwoFourSharpAngleBudget.lean`, successful
   [CI #39461412546](https://github.com/Charlie-Wang-03/awards/actions/runs/39461412546),
   3203 jobs, no `sorryAx`.
   For `lambda=pi/(2+delta)`, `0<=delta<1/2`, the bound
   `A<=delta*lambda`, `B,C,D<=pi-lambda` contradicts
   `A+B+C+D=2*pi`.

4. **Genuine strict exposure of ALL n=2 centres (unconditional).**
   `PlanarLowerTwoAllCentresExposed.lean`, successful
   [CI #39461956148](https://github.com/Charlie-Wang-03/awards/actions/runs/39461956148),
   3445 jobs; `lower_two_all_centres_strictlyExposed` depends only on
   `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
   Derivation uses actual `sum(centreQuotient)<=2` and the certified
   identity `floorExcess+positiveSupport=sum` to prove
   `positiveSupport<=2`, then actual transition-interval geometry.

5. **Prior root WIP branch integration:** fixed n=2 four-centre *no-top*
   branch and re-checked three dedicated WIP workflows:
   [#39457777100](https://github.com/Charlie-Wang-03/awards/actions/runs/39457777100),
   [#39457777215](https://github.com/Charlie-Wang-03/awards/actions/runs/39457777215),
   [#39457777108](https://github.com/Charlie-Wang-03/awards/actions/runs/39457777108)
   all PASS. The one admitted global `sorryAx` remains expected.

## Current next-step frontiers and in-flight checks

- `PlanarLowerTwoFourSharpCrossingObstruction.lean` bridges actual exponent-one
  sharpness, all-centres strict exposure, true convex-hull exclusions, the
  pre-existing `CrossingDiagonalsQuadrilateralAngleSum.lean`, and the
  certified numeric contradiction *conditional on an actual crossing quartet*.
  Initial CI [#39462168259](https://github.com/Charlie-Wang-03/awards/actions/runs/39462168259)
  failed at a **deterministic heartbeat limit in its historical quadrilateral
  angle-sum dependency**, not a fabricated theorem; the dependency's budget
  was raised and a newer focused run was triggered. Treat as pending until PASS.
- `FourPlanarRadonDependence.lean` NOW CERTIFIED: four planar points
  are not affinely independent and have a genuine Radon convex-hull
  partition. [CI #39462935746](https://github.com/Charlie-Wang-03/awards/actions/runs/39462935746)
  **PASS**, 3204 jobs, axioms `[propext, Classical.choice, Quot.sound]`.
- `FourPlanarRadonCrossingExtraction.lean` is the next step: enumerate the
  sixteen possible Fin4 membership patterns in a Radon partition,
  reject empty and singleton sides using the genuine convex-hull
  exclusions, and yield one of the three true pairwise crossing
  perfect matchings. Dedicated CI launched and not yet certified.


### Exact geometric bridge needed for an unconditional n=2 / four-centre result

A) The now-proved actual strict exposure forbids any of the four selected
vertices from lying in the convex hull of the other three; an existing
`four_strictlyExposed_convexHull_exclusions` lemma makes this explicit.

B) Apply the **finite planar Radon partition** to the four selected points.
A 0+4 or 4+0 partition cannot yield an intersection with an empty hull;
a 1+3 or 3+1 partition contradicts strict exposure. Thus the Radon partition
must have 2+2 elements. Its intersecting convex hulls are precisely two
crossing opposite segments. *This 2+2 extraction is the missing Lean lemma*,
not a theorem already obtained by this checkpoint.

C) Label the four points in cyclic order with the proposed exponent-one
centre in the first position. `CrossingDiagonalsQuadrilateralAngleSum`
then gives the four-angle sum 2*pi, while
`concrete_unit_deficit_is_sharp` gives its vertex angle <=delta*lambda;
the other three angle caps and the numeric contradiction discharge
the configuration.

This is a valid mathematical reduction; it does not yet close the full
four-point Lean theorem, and does not settle arbitrary-size n=2 or the
much larger unrestricted six-source payment for n>=3.

## Engineering observations

- `CutProjectiveBandPartition.lean`, `CutProjectiveBandOccupancy.lean`,
  `CutProjectiveBandBudget.lean` have been brought to independent kernel PASS.
- The old full-tree Fast Incremental Lean still has unrelated historical
  module failures; do not conflate them with extra admitted root `sorry`s.
- No new root axioms or unapproved hole/surplus credits were introduced.


## Addendum — 2026-10-21 Radon and sharp-centre closure

The statements above saying that Radon 2+2 extraction or the
crossing-diagonal sharp obstruction were still outstanding are
superseded by the following **independently kernel-audited** evidence:

- `FourPlanarRadonCrossingExtraction.lean`:
  `four_planar_hull_exclusions_force_crossing` proves a genuine
  crossing pair among three possible pairings from the four *actual*
  convex-hull exclusions, via sixteen exhaustive Radon-membership
  branches. [CI #39464265535](https://github.com/Charlie-Wang-03/awards/actions/runs/39464265535)
  **PASS**, 3209 Lake jobs; no `sorryAx`.
- `CrossingDiagonalsQuadrilateralAngleSum.lean` was repaired in the
  genuine triangle-angle-sum proof (in particular, the meeting point
  may coincide with one of the other diagonal endpoints).
  `crossing_diagonals_four_angles_sum_two_pi` and
  `PlanarLowerTwoFourSharpCrossingObstruction.lean`'s
  `lower_two_no_sharp_of_crossing_diagonals` both pass
  [CI #39551313684](https://github.com/Charlie-Wang-03/awards/actions/runs/39551313684),
  3456 jobs and printed axioms `[propext, Classical.choice, Quot.sound]`.
- The actual `Fin 4` geometric theorem
  `lower_two_four_no_sharp_fin_four` closes the three crossing
  configurations for EVERY proposed exponent-one vertex using the
  genuine `CentreProjectiveCycle` data.
  [CI #39551313787](https://github.com/Charlie-Wang-03/awards/actions/runs/39551313787)
  **PASS**, 3460 jobs, printed axioms
  `[propext, Classical.choice, Quot.sound]`.

The next, **not yet certified at this addendum**, bridge is to avoid
transporting centre cycles when converting an arbitrary type `V`
with `Fintype.card V = 4` into `Fin 4`. The new file
`PlanarLowerTwoFourActualQuartet.lean` uses the Fin4 Radon partition
ONLY for the selected four point positions, while keeping all quotient
and exponent data on the original `V`. The subsequent
`PlanarLowerTwoFourUnconditionalCapacity.lean` derives the genuine
unconditional capacity from this quartet theorem and an equivalence
`Fin 4 ≃ V`. Do not count either theorem as kernel-certified
until its dedicated CI succeeds.

The sole unrestricted six-source global `sorry` in the root WIP
remains open. Even complete closure of n=2 with four vertices is a
subcase, not the original JSP-000404 proof.
