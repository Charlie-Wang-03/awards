# JSP-000404 — Actual projected profile loss and translated duplicate debt
Date: 2026-10-15
Branch: `research/jsp-000404-sharp-centre`

## Fixed verified input

- `ResidualLossWords.lossCompletionWords_card_eq_totalDyadicProfileLoss`:
  under the ordinary exponent and palette bounds, the cardinality of the
  **original**, same-coordinate-pairwise-disjoint loss completion union is
  exactly `totalDyadicProfileLoss exponent (projectedFree C)`.
- `ResidualLossCoordinateSlices.two_mul_total_translatedLossSliceWords_card`:
  twice the sum of sizes of *different* translated coordinate slices equals
  the projected-loss target mass. This equality does not assert that different
  slices are mutually disjoint.
- `ResidualLossCrossCoordinateEdgeAvoidance.translatedLossSliceWords_cross_collision_edge_colour`:
  distinct coordinate slices can share a word only when two different loss
  owners are joined by a retained edge having the colour of one chosen
  flip coordinate.
- `ResidualLossCrossCoordinateEdgeAvoidance.two_mul_translatedLossSlice_union_card_of_edge_avoidance`:
  explicit complete retained-edge flip avoidance is **sufficient** for
  zero cross-coordinate loss collisions, but not known to follow from planar
  `AngleCap`. Independent CI 38713494504: PASS.

## New unconditional defect conservation

`ResidualLossDuplicateDebtLedger.lean` defines:

```text
U = ⋃_(c : Fin n) translatedLossSliceWords(C,k,choice,c)
D = (∑_(c : Fin n) |translatedLossSliceWords(C,k,choice,c)|) - |U|
```

The unconditional equality

```text
2 |U| + 2 D = ∑_(v ∈ projectedLossVertices(C,k)) 2^k(v)
```

is kernel-checked, with no `sorryAx`, in GitHub Actions run
**38715791900: SUCCESS**.

Two further Lean theorems have been submitted:

1. `positive_loss_duplicateDebt_has_slice_collision`: positive `D`
   forces two different coordinate slices to share an actual Boolean word.
2. `positive_loss_duplicateDebt_has_retained_edge`: positive `D` forces
   two **distinct projected-loss owners** connected by a retained edge
   whose colour equals the chosen flip coordinate of one owner.

Their **updated** independent CI must be checked before claiming them as
kernel-certified. They are necessary witnesses, not converses.

## Exact link to the real six-source payment term

New `ResidualLossProfileExactUnionLedger.lean` builds on
`ResidualLossWords.lean` and proves, subject to successful independent CI:

```text
totalDyadicProfileLoss k (projectedFree C)
       = |U| + D
```

This is strictly more relevant to the outstanding lower-branch `sorry`
than the earlier twice-the-target mass identity, because it uses the
actual dyadic profile-loss term of the existing payment interfaces.

It does NOT convert `U` into true Boolean holes or turn `D` into a
positive payment credit. Global shared-word multiplicities, occupied
non-hole targets, and non-reuse of all six classes of payment remain open.

## Lean infrastructure repairs, kernel-check boundary

- `AggregateSplitTree.lean`: explicit universe and decidable equality
  instance fixes; independent CI **38715842964: PASS**.
- `SupportLeTwoTransitionInterval.lean`: independent CI
  **38714423740: PASS**.
- `ConcreteSharpCentre.lean`: use the actually verified concrete support-one
  existence certificate and correct the exact width/angle derivation;
  independent CI **38716523654: PASS**.
- Historical Fast Incremental CI is **not** fully green; separate legacy
  modules still fail. Focused passes are not a blanket full-build claim.

The only admitted `sorry` in `PlanarLowerBranchProofAdmittedWIP.lean`
remains unchanged. JSP-000404 has **not** been fully proved or disproved.
