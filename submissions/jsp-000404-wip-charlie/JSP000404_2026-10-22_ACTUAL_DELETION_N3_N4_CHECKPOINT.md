# JSP-000404 — 2026-10-22 actual deletion and exact n=3/n=4 terminal handoff

Branch: `research/jsp-000404-sharp-centre`.

## Scientific status

This work remains **research-only partial formalization**, not a full proof or disproof. The sole executable root `sorry` is intentionally retained in `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`; its `#print axioms` reports `sorryAx`. The missing theorem is the **global non-reusing actual six-source payment** including literal Boolean holes, all hard and mixed carrier classes, duplicate collision fibre debt, fifth-centre covered diagonal blockers, soft overlap, and projected loss. Local centre deletion/gap lemmas do **not** discharge this claim.

The last earlier completed fast-incremental all-target run:
https://github.com/Charlie-Wang-03/awards/actions/runs/39758411689
failed with 180 diagnostics in 17 modules (some cascading); **not a successful complete Lean build**.

## Independently kernel-verified results in this session

1. **Three repaired exact-deletion/unit-slot modules**: 
   - `ConcreteAdjacentDoubleDeletionRigidity.lean`
   - `SixPointUnitGapSlots.lean`
   - `SixPointNFourEquality.lean`

   Successful focused check:
   https://github.com/Charlie-Wang-03/awards/actions/runs/39761398448
   — 3535 Lake jobs, the printed exported theorem axioms use only `propext, Classical.choice, Quot.sound`.

   Mathematical consequences:
   - Two adjacent zero-exponent-gain *concrete* deletions at a high survivor force at least two of three immediate parent quotient gaps to vanish under the theorem's geometric/ray adjacency premises.
   - The true dependent sigma type of original-centre unit quotient gap slots has cardinality exactly the sum of `unitSupport` over actual centres. Under the six-centre top/5-minima exponent profile, this cardinality is at most ten.
   - At `n=4`, with one top exponent three, five minima exponent one, **conditional on equality** of ten unit slots, each minimum centre has exactly the positive quotient multiset `{1,1,2}` and full five-coordinate multiset `{0,0,1,1,2}`. Equality itself, and geometric impossibility, were *not* proved.

2. **Two actual n=3 exact unit/double quotient companions**:
   - New `ThreeFiveTwoExactUnitDoubleCentres.lean`
   - Focused success: https://github.com/Charlie-Wang-03/awards/actions/runs/39762843578
   - 3537 Lake jobs, axiom check contains NO `sorryAx`.

   Starting from the previously verified AngleCap `two_saturated_next_among_four_n3`, the new theorem gives, among four distinct original exponent-one centres at `t=3+delta`, at least two different ones whose quotient vectors each have **exactly one unit and one double** entry. This is a necessary condition of the `n=3` five-centre **no-top** overweight motif A, NOT an exclusion of it. The new theorem is imported in the research umbrella.

3. Verified in the prior session and preserved: `ThreeFiveSaturatedUnitQuotients` establishes a `1+1+1` original-centre quotient companion in the `n=3` five-centre top+next overweight motif B; `SixPointSupportThreeOutletDichotomy` establishes a middle-or-end structural disjunction, with neither geometric exclusion nor actual deletion gain by itself.

## Additional new source in this session — check the latest CI before claiming completion

The intended **actual support-three concrete deletion alternative**, `SixPointSupportThreeActualDeletionOutlet.lean`, directly composes:
- `exists_sharp_pinned_support_three_shape_with_split`
- six-original-vertex `qmid` length-three / positive-count-one classification
- `support_three_left_hidden_nonTop_deletion_gain`
- `support_three_right_hidden_has_nonTop_deletion_gain`

It states that each actual support-three exponent-`n-3` minimum in a six-centre planar AngleCap sharp-top configuration has EITHER
- the explicit middle hidden positive quotient `[0,qHidden,0]`, or
- a **concrete original non-top vertex** whose deletion increases this original minimum centre's exponent by at least one.

This is a meaningful *local* obstruction-to-outlet reduction. It is NOT the global six-source payment or exclusion of the middle shape.

Focused workflows at this checkpoint:
- left/right gain: https://github.com/Charlie-Wang-03/awards/actions/runs/39763022626
- integrated reduction: https://github.com/Charlie-Wang-03/awards/actions/runs/39763022606

**Verification completed: BOTH focused CI runs PASS.**
- Left/right concrete gain:
  https://github.com/Charlie-Wang-03/awards/actions/runs/39763022626
  — 3536 Lake jobs, both theorem axiom audits are
  `[propext, Classical.choice, Quot.sound]`.
- Integrated middle-or-original-non-top-deletion alternative:
  https://github.com/Charlie-Wang-03/awards/actions/runs/39763022606
  — 3537 Lake jobs, the concrete geometric composite
  `six_point_support_three_middle_or_concrete_nonTop_gain`
  depends on axioms `[propext, Classical.choice, Quot.sound]`,
  with **NO `sorryAx`**.

The earlier failed attempts were specifically caused by Lean list-rotation
period normalization; the actual `List.rotate_length` lemma resolved it.
The integrated theorem is now imported by the research umbrella
`JSP000404Research.lean`. It is the strongest actually kernel-checked
support-three **local outlet** so far, and reduces the open branch to an
explicit middle hidden `[0,qHidden,0]` quotient case unless a particular
non-top deletion gain is available. It does **NOT** prove the global
non-reusing simultaneous payment, show that this middle geometry is impossible,
or close the admitted lower branch.

## Next genuine mathematics

- n=3 five-original-centre motif A: exclude or globally compensate two distinct exact `2+1` quotient centres.
- n=3 five-original-centre motif B: exclude or globally compensate an original `1+1+1` companion at a top+next profile.
- Six-original-centre support-three terminal: deal with the **central hidden** shape `[0,qHidden,0]` or find a global payment mechanism that works without excluding it.
- General cardinality: discharge the genuinely global non-reused six-source true-hole/surplus payment; do not rebrand soft covered words or duplicate diagonal targets as Boolean holes.

None of these three mathematical endpoints are currently closed by the results above. No new hypotheses were silently added to the admitted root theorem.


## Follow-on session: 2026-10-22 — strict-exposure, half-cap, concrete-gain trichotomy

### Certified mathematical advance (kernel PASS)

New `JSP000404Research/SixPointExposedOrTwoHalfCapBridgesOrGain.lean` contains the actual AngleCap trichotomy
`six_point_support_three_exposed_or_two_halfcap_bridges_or_actual_gain`.

Given a genuine six-original-point configuration with sharp top, n>=4,
0<=delta<1/2, a distinct minimum centre i with
`centreExponent C t = n-3` and `positiveSupport (centreQuotient C t) = 3`,
ONE of the following is necessary:

1. `StrictlyExposedAt p i`.
2. `TwoSeparatedHalfCapBridges (p := p) top i lam` — four distinct
   actual neighbouring original rays form TWO disjoint pairs, each pair's
   angle at i < lam/2, while all four angles from the top to those rays,
   and all four cross-pair angles at i, are strictly > lam.
3. There exists an ACTUAL original non-top deleted vertex r, r != i,
   with `centreExponent C t + 1 <= centreExponent (C.restrictDelete r ...) t`.

The theorem composes the preexisting certified middle-hidden cross-cluster
geometry and genuine local deletion gains, and uses no extra geometric
hypothesis beyond its stated AngleCap/SharpAt assumptions.

**CI PASS**
https://github.com/Charlie-Wang-03/awards/actions/runs/39768836560
3551 Lake jobs. `#print axioms`: `[propext, Classical.choice, Quot.sound]`;
**no `sorryAx`**. The theorem is imported in `JSP000404Research.lean`.

It reduces the open local geometry to a narrowly constrained exposed
case or two disjoint short bridges when direct deletion gain is unavailable.
Neither alternative has yet been proved impossible, nor paid by genuinely
unreserved global Boolean holes.

### Certified legacy compiler repairs

**CI PASS:** https://github.com/Charlie-Wang-03/awards/actions/runs/39768836464
(3544 Lake jobs), for:
- `AdjacentMinimumRayRigidity.lean`
- `MinimumAdjacentDoubleDeletion.lean`
- `SupportThreeMiddleOrDeletionGain.lean`

These restore direct second-deletion exponent equality and the formal
three-gap sparsity of adjacent concrete minimum deletions. The middle-hidden
vs actual non-top deletion alternative in the older named module compiles
without `sorryAx`; these are NOT closed global payment obligations.

**CI PASS:** https://github.com/Charlie-Wang-03/awards/actions/runs/39769193728
(8962 Lake jobs), for `MergeLastPalettePullback.lean`.
All five printed theorems have no `sorryAx`.
The exact fibre of `mergeLastColor` identifies old 0/n and NOTHING ELSE:
equal merged palettes coincide at all positive interior colours and can
differ only through the 0/n boundary representative, under the stated
per-palette no-double-boundary premise.

### Still pending at this checkpoint

`UnitSameSignOccurrence.lean` was repaired and has a focused build at
https://github.com/Charlie-Wang-03/awards/actions/runs/39769762710.
Status at writing: **in progress, NOT yet claimed kernel certified**.
Earlier run #39769065818 failed on three concrete tactic/elaboration errors
(missing `TransitionQuotientOccurs` simp symbol, incorrect induction
argument, reversed natural-number equality). All three were corrected
in commit `c83fd73d02989548609a0bbfdc981284ed2fb3f9`.

The full `JSP000404Research` import closure remains unverified because the
most recently completed full-tree incremental run
https://github.com/Charlie-Wang-03/awards/actions/runs/39763615218
failed on many LEGACY modules. A newer run
https://github.com/Charlie-Wang-03/awards/actions/runs/39769762762
is still in progress at this checkpoint. Do NOT treat focused PASS as full
repository compilation.

The sole executable admitted theorem remains
`PlanarLowerBranchProofAdmittedWIP.lean` — **exactly one genuine
`sorry`, with `sorryAx`**. The global nonreused six-source payment,
real Boolean true holes, mixed/soft/twin sources, projected loss and
collision-fibre compensation are NOT closed. No mathematical proof or
counterexample to JSP-000404 is claimed.
