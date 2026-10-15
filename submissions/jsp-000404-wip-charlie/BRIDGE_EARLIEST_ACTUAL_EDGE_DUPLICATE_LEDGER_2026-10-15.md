# JSP-000404 — Exact earliest-hit retained-edge duplicate-debt ledger (2026-10-15)

Research branch: `research/jsp-000404-sharp-centre`.
Research status: **incomplete proof / no disproof established**.
The admitted main root `PlanarLowerBranchProofAdmittedWIP.lean`
continues to contain exactly one executable `sorry`.
No new axiom or replacement sorry is allowed in certified work.

## 1. Exact first-prior-coordinate ownership (certified)

Module: `JSP000404Research/ResidualLossEarliestCollision.lean`.
Focused GitHub Actions **38761014451 SUCCESS**, 3,311 jobs.
`translatedLossDuplicateDebt_eq_sum_earliestPairWords` has
axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

Let `T_i` denote the original actual translated-loss slice.
For each later coordinate i, and strictly earlier j, define

```text
E_(i,j) = (T_i ∩ T_j) \ ⋃_(k<j) T_k.
```

Then

```text
D_dup = ∑_(i<n) ∑_(j<i) |E_(i,j)|.
```

Each repeated word in a fixed later `T_i` is assigned to its
unique earliest preceding coordinate j. It may still reappear as
a separate duplicate EVENT at a different later i.

## 2. Exact actual source/blocker carrier partition (certified)

Module: `ResidualLossEarliestActualEdgeCarrier.lean`.
Focused GitHub Actions **38761677516 SUCCESS**, 3,312 jobs.
Kernel-checked declarations, each without `sorryAx`:

- `lossEarliestPairWords_disjoint_of_lt`
- `lossEarliestPairWords_pairwiseDisjoint`
- `lossEarliestPairWords_eq_biUnion_actualEdge`
- `lossEarliestActualEdgeCarrier_pairwiseDisjoint`
- `lossEarliestPairWords_card_eq_actualEdge_sum`

For c ≠ d, each `E_(c,d)` is exactly the union of
`crossLossPairWords C c d p \ lossPrefixUnion T d` over
contributing actual pair `p=(v,w)`. These pair carriers are
disjoint for FIXED coordinates c,d, and every p is certified
to have a genuine retained connecting edge whose actual
colour is c or d.

## 3. Exact GLOBAL retained-edge triple-index identity (certified)

Module: `ResidualLossEarliestActualEdgeGlobalLedger.lean`.
Focused GitHub Actions **38761851516 SUCCESS**, 3,313 jobs.
`translatedLossDuplicateDebt_eq_sum_earliest_actual_edges`
has only axioms `[propext, Classical.choice, Quot.sound]`,
no `sorryAx`.

```text
D_dup
 = ∑_(0≤j<i<n) ∑_(p∈crossLossConflictPairs(i,j))
       |crossLossPairWords(i,j,p) \ ⋃_(k<j) T_k|.
```

The outer (i,j) and inner p indices are REAL sources of
repetition in the original finite Boolean word families.
No dyadic upper-envelope loss is introduced.
The independent sorry-free `VerifiedOverlapRewire.lean` root
now imports this certified global ledger; its triggered root CI
must be checked separately and is not presumed green here.

## 4. Exact TERMINAL six-source iff (certified)

Module: `ResidualTerminalTwinExactEarliestEdgeFrontier.lean`.
Focused GitHub Actions **38762057743 SUCCESS**, 3,400 jobs.
`terminalTwinSixSourcePayment_iff_earliestActualEdgeFrontier`
has only axioms `[propext, Classical.choice, Quot.sound]`,
no `sorryAx`.

It proves a literal two-way equivalence of the pre-existing
six-source inequality and the existence of a retained-active
choice paying:

```text
terminalTwinOtherFiveDebt
 + |chosen actual same-colour covered loss blocker union|
 + exact earliest (i,j,p) actual-edge duplicate mass
 <= |outside true holes| + genuinely unreserved surplus.
```

The inequality on the right remains an EXISTENTIAL CONDITION,
not a theorem established from AngleCap. No external hole
or unreserved surplus is conjured by this rewrite.

## 5. Planar lower branch bridge and finer local nonreuse

`PlanarLowerBranchEarliestActualEdgeFrontier.lean` has
been submitted as a conditional consequence of the exact
terminal iff. Its own focused CI must be checked.
Likewise `ResidualLossEarliestActualEdgeNonreuse.lean`
formulates disjointness of earliest-event carriers across
distinct predecessor coordinates for FIXED later c.
It is not a cross-later-i global nonreuse result.
Kernel statuses of these two were not final at this document
checkpoint; do not infer success from the above results.

## 6. Legacy Lean repairs

The following historical modules were repaired and built
together in focused CI **38761178625 SUCCESS**, 3,456 jobs:

- `BoundedLoadHall.lean` (correct filter membership elimination);
- `SupportThreeTransitionDichotomy.lean` (correct post-cases
  canonical first/rest list witness);
- `GeneralZeroGapSmallAngle.lean` (canonical `lam` binder
  before `AngleCap p lam`).

`ResidualUnsafeWitnessCount.lean` also had explicit
`Fin (n+1)` value-projection correction submitted and
focused CI **38762354999 SUCCESS**.

## 7. Honest frontier / do not silently discharge

The remaining obstacle is NOT the finite combinatorial
decomposition of duplicate mass. That is now completely
explicit and exact. It is the GLOBAL, non-reusing payment
across (i) all other terminal debt classes, (ii) truly
covered translated-loss blocker mass, (iii) the exact
earliest-edge duplicate events, using only (iv) genuine
Boolean holes OUTSIDE all translated loss words and
(v) truly unreserved dyadic surplus.

No claim that distinct (i,j,p) events across different
later i have disjoint Boolean-word sets follows from
the certified local partitions. Source/blocker carriers
are not themselves free holes.

The geometric `AngleCap` hypotheses and ordered-edge
colour rigidity have yet to imply the required global
matching or nonreuse inequality. Consequently the main
admitted WIP root still has its one executable `sorry`.
Do not claim a full Lean build from focused successes.
