# JSP-000404 — Loss edge-avoidance reduction and Lean repairs (2026-10-15)

Branch: `research/jsp-000404-sharp-centre`.
All work here is research-only. The full original JSP-000404 problem is
**not** proved or disproved; the sole admitted global payment `sorry` in
`PlanarLowerBranchProofAdmittedWIP.lean` is still present.

## Kernel-checked mathematical result

Module: `JSP000404Research/ResidualLossCrossCoordinateEdgeAvoidance.lean`.
Independent GitHub Actions run **38713494504: SUCCESS**. Axiom printouts
for both newly established results omit `sorryAx`.

For any projected-loss colouring `C`, exponent profile `k`, and chosen
coordinate function `choice : V → Fin n`, define
`LossFlipAvoidsRetainedEdges C k choice`: on **every retained edge between
two projected-loss vertices**, its colour differs from the chosen flip
coordinate at either endpoint.

The new theorem
`translatedLossSliceWords_disjoint_of_edge_avoidance` says that, under
the already established exponent and active-palette bounds, avoidance
implies **pairwise disjointness between different coordinate slices**.

The new theorem
`two_mul_translatedLossSlice_union_card_of_edge_avoidance` proves the
following *exact cardinality of the actual Boolean union*:

```text
2 * |⋃_(c : Fin n) translatedLossSliceWords(C,k,choice,c)|
    = ∑_(v in projectedLossVertices(C,k)) 2^(k(v)).
```

This strengthens the previous unconditional equality for the **sum of
individual slice cardinalities**. The added avoidance assumption is
material: it is **not** known to follow from genuine planar `AngleCap`.
Thus neither the new conditional union identity nor the old unconditional
sum identity automatically gives a global true-hole credit.

The source-level necessary collision witness theorem remains unconditional:
a shared word in distinct loss slices forces a retained edge between
distinct projected-loss centres, with its colour one of the two chosen
flip coordinates.

## Verified Lean repair

`ResidualChildWidthHardStop.lean` now builds with Lean 4.34.0:
GitHub Actions run **38713102832: SUCCESS**. The geometric width-reduction
hard stop is a **counterexample to a tempting recursive lemma**, not a
counterexample to JSP-000404. It prevents treating an entire not-sink child
as if it automatically had one less unit of DirectionData width.

## Additional repair work and verification boundary

The following legacy sources have received targeted elaboration / API
repairs in this research branch:

- `ConcreteHighExponentExposure.lean`: prior focused CI
  **38689363462: SUCCESS**.
- `OneTransitionSupportInterval.lean`: corrected implicit `lam` binding,
  obsolete list-nil lemma, separate nil/cons ray-list normalizations, and
  positivity argument; independent CI added (result must be checked).
- `ConcreteOneSupportInterval.lean`: analogous repairs; independent CI
  added (result must be checked).
- `GeneralMixedExteriorContradiction.lean`,
  `ThirdLayerTransitionPacking.lean`, and
  `ResidualChildWidthHardStop.lean`: obsolete
  `Mathlib.Data.Matrix.Notation` import replaced with extant
  `Mathlib.Data.Matrix.Basic`. The three-module combined CI is not yet
  green: other historical dependencies including
  `FourCentreTransitionCases` and `FourCentreSupportTwoSmallAngle`
  still have independent Lean errors.

No full-workspace or admitted-root kernel closure is claimed.

## Exact outstanding mathematical obligation

The global six-source inequality still requires simultaneous, globally
**non-reusing** allocation of all remaining debt: projected profile loss,
soft overlap, movable forward/reverse hard mass, terminal equal-exponent
twins, and ascending/descending mixed-rigid masses.

Eligible credits are only **genuine Boolean holes** and
**independently unreserved dyadic surplus**. Neither already-covered soft
words, bridge candidate slots, nor previously reserved surplus can be
silently counted as credits.

The new loss edge-avoidance reduction isolates a *sufficient* obstruction
criterion for the translated projected-loss subproblem, not a planar
proof of avoidance, a global payment theorem, or a closure of the main
`sorry`.
