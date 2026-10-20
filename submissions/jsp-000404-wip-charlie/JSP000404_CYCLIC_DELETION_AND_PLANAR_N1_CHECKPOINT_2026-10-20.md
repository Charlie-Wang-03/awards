# JSP-000404 — Cyclic deletion, occupied-band budget and n=1 closure

Date: 2026-10-20. Research branch: `research/jsp-000404-sharp-centre`.
This is a factual research checkpoint, **not** a full proof or disproof.

## A. Lean-verified deletion lemmas

1. `SecondDeletionTwoStableMinima.lean`: quantitative survivor stability and two unchanged minimum-layer survivors; kernel CI [39440782888](https://github.com/Charlie-Wang-03/awards/actions/runs/39440782888) **SUCCESS**.
2. `MiddleProjectiveGapDeletion.lean`: interior cyclic gap deletion repair; CI [39441617262](https://github.com/Charlie-Wang-03/awards/actions/runs/39441617262) **SUCCESS**.
3. `LastProjectiveGapDeletion.lean`: final angle deletion and exponent unit gain; CI [39445005818](https://github.com/Charlie-Wang-03/awards/actions/runs/39445005818) **SUCCESS**.
4. `CyclicGapDeletionAfterFirst.lean`: `listExponent_gain_delete_after_first`, using the actual next angle or the wraparound value `a + pi` when the suffix is empty; CI [39445593871](https://github.com/Charlie-Wang-03/awards/actions/runs/39445593871) **SUCCESS**.

These statements do **not** establish the existence of a globally compensated deletion or the required six-source payment.

## B. Genuine one-dimensional missing-band results

1. `CyclicBandMissing.lean`: all six audited exact integer missing-band and natural-floor comparison lemmas; CI [39446607450](https://github.com/Charlie-Wang-03/awards/actions/runs/39446607450) **SUCCESS** (8929 jobs). All six `#print axioms` outputs are `[propext, Classical.choice, Quot.sound]`.
2. `ScaledCyclicBandBudget.lean`: cyclic gap exponent bounded by missing bands, together with new `listExponent_floor_cyclicGaps_add_occupied_le`, asserting
```text
listExponent ((cyclicGapsAt t (a :: xs)).map Nat.floor)
 + (floorBandList (a :: xs)).toFinset.card <= n + 1
```
for nonnegative nondecreasing coordinates below `t=n+delta`, `0<=delta<1`.
CI [39448767002](https://github.com/Charlie-Wang-03/awards/actions/runs/39448767002) **SUCCESS** (8937 jobs), and the new theorem prints only `[propext, Classical.choice, Quot.sound]`.

These prove a complete **one-dimensional** cyclic-gap budget. They do **not** infer a globally disjoint hole allocation or solve the projection/mixed/twin/net debts.

## C. A genuine planar n=1 branch is now closed in the main WIP

`PlanarFirstBranchNoThree.lean` already proves that `AngleCap` and
`n=1`, `0<=delta<1/2`, `t=1+delta`, `lam=pi/t`
force `card V<=2`. This genuine geometric result was not integrated
into the top-level `PlanarLowerBranchProofAdmittedWIP.lean` earlier.

The top-level proof now explicitly splits off `n=1`, derives
`card (ProjectionOrdered V)<=2` for the ACTUAL reindexed planar
configuration and applies the previously verified small-centre
dyadic capacity instead of the admitted global payment.

Dedicated independently sorry-free theorem:
`ProjectionOrdered.planar_lower_branch_n_one_dyadic_capacity`
in `PlanarLowerBranchOneCapacity.lean`.
CI [39448234992](https://github.com/Charlie-Wang-03/awards/actions/runs/39448234992)
**SUCCESS** (3507 jobs), printed axioms
`[propext, Classical.choice, Quot.sound]`.

Top-level WIP recompilation of the additional n=1 closed branch:
- [39447123802](https://github.com/Charlie-Wang-03/awards/actions/runs/39447123802) SUCCESS;
- [39447123818](https://github.com/Charlie-Wang-03/awards/actions/runs/39447123818) SUCCESS;
- [39447123917](https://github.com/Charlie-Wang-03/awards/actions/runs/39447123917) SUCCESS.

The remaining admitted WIP branch is consequently restricted to `n>=2`
and the other configurations not covered by genuine verified terminal cases.

## D. Still-open original theorem

Exactly ONE intentionally admitted executable `sorry` remains in
`PlanarLowerBranchProofAdmittedWIP.lean`. It requires the unrestricted
global, **non-reusing** six-source geometric payment. In particular,
remaining soft / forward / reverse / twin / mixed liabilities, genuine
covered translated-loss carriers and cross-coordinate duplicate debt
cannot be paid by reusing already consumed true holes or by treating
covered Boolean words as holes.

The whole-tree Fast Incremental Lean CI has additional historical
compiler errors; focused PASS is not whole-tree PASS. An
arbitrary-cardinality source-closure gap remains independently OPEN.
Neither a complete proof nor a certified counterexample is known in
this working branch.

## E. Current immediate continuation

1. Complete the adjacent `ProjectiveGapScaling.lean` kernel regression
   and the general projective/cut-coordinate occupancy mapping. Do not
   infer their success from the one-dimensional budget.
2. Keep all legacy Lean-error repairs isolated from the unproved
   `AngleCap` six-source allocation.
3. Search for a genuinely nonreusing global allocation theorem, or
   an actual counterexample. Merely changing an equivalent frontier
   hypothesis does not discharge the residual `sorry`.
