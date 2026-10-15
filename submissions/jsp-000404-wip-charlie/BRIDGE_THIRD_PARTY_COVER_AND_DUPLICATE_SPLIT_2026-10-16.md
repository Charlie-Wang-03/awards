# JSP-000404 — Third-party cover obstruction and exact collision debt split

Date: 2026-10-16. Downstream branch: `research/jsp-000404-sharp-centre`.

**Status:** Genuine progress on Lean-checked necessary conditions and the exact terminal accounting structure. **NOT a complete proof or disproof.** `PlanarLowerBranchProofAdmittedWIP.lean` still has one executable `sorry`. No extra `sorry`/axiom was added to any of the new certified proofs.

## Original exact triple-index loss collision ledger

As proved in `ResidualLossEarliestActualEdgeGlobalLedger.lean`, focused CI **38761851516 SUCCESS**, the original `translatedLossDuplicateDebt` equals the sum over later coordinate `i`, earliest prior coordinate `j<i`, and the actual loss-source/blocker vertex pair `p=(v,w)` of genuine earliest-hit collision word set cardinalities. This is an **equality**, not a dyadic overestimate.

## Two distinct original completion owners

Module: `ResidualLossEarliestEdgeTwoOwnerCorners.lean`. Focused CI **38771471851 SUCCESS**, 3,321 jobs, only Lean foundational axioms (no `sorryAx`).

For every actual first-hit loss collision `x` of distinct chosen coordinates `c,d` and endpoints `v,w`, the two Boolean neighbours `flip(x,c)`, `flip(x,d)` are distinct and belong to the ORIGINAL retained completion cubes `B_v`, `B_w` respectively; `v ≠ w`. If the actual chosen coordinate is retained-active for every projected loss vertex, then `x ∉ B_v` and `x ∉ B_w`.

These are real original cube owners, not arbitrary placeholders. This does **not** assert that `x` is globally uncovered: a third vertex may cover it.

## Exact third-party cover criterion

Module: `ResidualLossEarliestEdgeThirdPartyCover.lean`. Focused CI **38772204893 SUCCESS**, 3,322 jobs, no `sorryAx`.

Under the same genuine active-choice condition:

```text
x ∈ coveredCompletionWords C
  ↔ ∃ u ≠ v, u ≠ w, x ∈ retainedCompletionWords C u

x ∈ lossLedgerGlobalTrueHoles C
  ↔ ¬ ∃ u ≠ v, u ≠ w, x ∈ retainedCompletionWords C u
```

This EXACTLY separates the two possible original coverage statuses of a genuine loss collision. The **third-party covering vertex has not been excluded by planar AngleCap**.

## Exact COVERED / TRUE-HOLE duplicate debt split

Module: `ResidualLossEarliestEdgeCoveredSplit.lean`. Focused CI **38773117086 SUCCESS**, 3,324 jobs, no `sorryAx`.

```text
D_dup = D_dup_covered + D_dup_trueHole
```

The first sum includes genuine earliest-edge collision events whose Boolean word is in the original covered union, and (for active choices) each has an original third-party covering vertex. The second sum includes events whose Boolean word is globally uncovered. The full *event multiplicities* from the exact `(i,j,p)` ledger are maintained. These two `Nat` terms are not necessarily the cardinalities of unions of pairwise disjoint GLOBAL word sets.

Every event's Boolean word is inside translated-loss union `U`, regardless of coverage status. Therefore neither piece automatically contributes a word in `lossLedgerOutsideTranslatedTrueHoles`, the genuine outside-`U` resource on the terminal right side.

## New terminal frontier — separate kernel result required

The file `ResidualTerminalTwinCoveredHoleEdgeFrontier.lean` rewrites the original six-source inequality in terms of:

```text
terminalTwinOtherFiveDebt
 + |real chosen-colour covered blocker union|
 + D_dup_covered + D_dup_trueHole
≤ |outside translated-loss true holes| + genuinely unreserved surplus.
```

This is still an EXISTENTIAL PAYMENT condition on an active choice; its focused terminal CI must be checked before stating it is certified. Even if the IFF compiles, it is an EQUIVALENCE and NOT the missing global payment proof.

## Independent Lean compilation repairs

Confirmed focused SUCCESS without `sorryAx`:

- **38772034415:** `FarthestStrictExposure`, `CanonicalSignOrder`, `SixPointPhaseGapArithmetic`; fixed geometry rewrite, real norm-add-square specialization, half-plane sign direction, gap arithmetic.
- **38772578052:** `FullMassPointwiseRemainder`; repaired `List.Forall₂` induction and exact delta remainder.
- **38772914851:** `ProjectiveBandOccupancy`; repaired AngleCap binder and the definitional unfolding of the real edge-color constructor.

The separate `SupportThreeMiddleHiddenCanonicalSigns` focused job was still under verification at this checkpoint.

## What remains mathematically unsolved

The original six-source payment demands a globally non-reusing assignment into ONLY outside-`U` true holes and genuinely unreserved dyadic surplus for all other five debts, actual covered loss blockers, and BOTH collision-duplicate subdebt types.

No existing theorem shows a suitable assignment or numerical payment. In particular:
- Third-party owners of covered collisions have NOT been ruled out geometrically.
- Inside-`U` true-hole collision events are NOT outside-`U` refund assets.
- Unique edge indices and local pairwise disjointness do NOT imply globally disjoint Boolean word supports across distinct later coordinates.
- A claim about a new true-hole refund cannot be inferred just from flipping c or d: both one-flip ancestors are already covered.

The latest full Fast Incremental Lean workflow was still failing on historical modules; focused successes are not a full workspace success.
