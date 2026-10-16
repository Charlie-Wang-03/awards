# JSP-000404 — Mixed Interior Proof Ledger (2026-10-16)

Branch: `research/jsp-000404-sharp-centre`. This is a factual
checkpoint, **not** a completed proof or an upstream award submission.

## Verified geometric dependencies

1. `TriangleConvexCone.lean`: the positive displacement cone
   and actual Euclidean angle splitting for points in a three-point
   convex hull. CI
   [38919300967](https://github.com/Charlie-Wang-03/awards/actions/runs/38919300967)
   **SUCCESS**, 3,224 jobs. The principal declarations have standard
   Lean axioms only, no `sorryAx`.
2. `GeneralMixedExteriorContradiction.lean`: excludes a mixed fourth
   centre OUTSIDE the triangle of the three distinguished centres
   in an arbitrary finite ambient point set, with genuine
   `AngleCap`, centre exponent and quotient-support premises.
   CI [38918434932](https://github.com/Charlie-Wang-03/awards/actions/runs/38918434932)
   **SUCCESS**, 3,463 jobs; no `sorryAx`.
3. `GeneralMixedExteriorActualHull.lean`: the positive logical
   corollary that this fourth centre belongs to the triangle,
   with the SAME genuine centre hypotheses and no additional
   transition-certificate assumptions.
   CI [38924379282](https://github.com/Charlie-Wang-03/awards/actions/runs/38924379282)
   **SUCCESS**, 3,464 jobs; no `sorryAx`.
4. `FourCentreMixedInteriorHiddenAngle.lean`:
   `mixed_inside_hidden_angle_weakened_fin_four` has its own
   `#print axioms` report containing only
   `[propext, Classical.choice, Quot.sound]`, as seen in
   [run 38923851661](https://github.com/Charlie-Wang-03/awards/actions/runs/38923851661).
   This run as a whole **FAILED** later, in the separate
   `FourCentreMixedInteriorContradiction.lean` module.
   Its theorem proves
   `((n-1)-delta)*lam <= angle(p s, p b, p c)`
   under the actual mixed-centre premises and an interior
   fourth vertex; it is not a global payment certificate.

## Current interior terminal repair

The failure of
[38923851661](https://github.com/Charlie-Wang-03/awards/actions/runs/38923851661)
was narrowed to a single missing commutation
`angle(p a, p b, p c) = angle(p c, p b, p a)`
before the final `linarith` calculation.
This was repaired in commit `4e378d2fc5bc275fed6769db75435d1a6dad4e1f`.
The exact-source focused run
[38924495684](https://github.com/Charlie-Wang-03/awards/actions/runs/38924495684)
must be checked for final outcome.

`FourCentreMixedTotalContradiction.lean` combines the
true-hypothesis four-centre hull inclusion with
`no_mixed_fourth_inside_fin_four` and has its own
focused run
[38924495644](https://github.com/Charlie-Wang-03/awards/actions/runs/38924495644).
It is a proposed **conditional four-centre pattern exclusion**
until the entire focused build is GREEN and its theorem axiom
audit contains no `sorryAx`.

`FourCentreMixedInteriorReduction.lean` was shortened from
approximately 146 lines to 57 lines, preserving its original strong
hidden-angle theorem statement and reducing its proof to the
weakened hidden-angle terminal under `delta >= 0`. Its
dedicated verification is
[38924734045](https://github.com/Charlie-Wang-03/awards/actions/runs/38924734045),
also requiring final CI confirmation.

## Root mathematical gap

The original
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`
still has **one** genuine executable `sorry` for the global
non-reusing payment across multiple terminal dyadic debt sources.
Even a complete four-centre mixed local geometry theorem does
**not** establish the arbitrary-cardinality six-source
outside-true-hole / unreserved-surplus capacity bound.

There are many historical legacy compilation failures in the
full incremental build. Focused successes must not be presented
as full-repository success. Future work should take the latest
full error census rather than reusing a historical total.
