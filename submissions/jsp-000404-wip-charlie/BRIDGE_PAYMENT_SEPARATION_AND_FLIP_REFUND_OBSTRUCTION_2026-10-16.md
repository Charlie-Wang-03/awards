# JSP-000404 — Payment-resource separation and chosen-flip obstruction

Date of checkpoint: 2026-10-16 (Asia/Tokyo).
Branch: `research/jsp-000404-sharp-centre`.
**JSP-000404 remains OPEN**. The admitted main root
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`
still contains its unique executable `sorry`. No axiom, hidden
surrogate or new `sorry` is introduced in the statements below.

## 1. Basis and exact duplicate-debt frontier

Previously certified:

- `translatedLossDuplicateDebt_eq_sum_earliest_actual_edges`
  (focused CI 38761851516 SUCCESS): original duplicate mass
  equals the exact sum indexed by later coordinate, earliest earlier
  coordinate and genuine source/blocker retained-edge carrier pair.
- `terminalTwinSixSourcePayment_iff_earliestActualEdgeFrontier`
  (focused CI 38762057743 SUCCESS): two-way equivalence with the
  original terminal six-source inequality, but its *global*
  external-hole/unreserved-surplus payment is an UNSOLVED condition.
- `planar_lower_branch_capacity_of_earliest_actualEdge_payment`
  (focused CI 38762579169 SUCCESS): conditional planar consequence.
- `VerifiedOverlapRewire.lean` re-import of exact global duplicate
  ledger (focused CI 38762776625 SUCCESS).
- `crossLossConflictPairs_no_reverse_high_coordinate`
  (focused CI 38763344562 SUCCESS): edge-pair LABEL nonreuse, not
  nonreuse of Boolean words or actual holes.

## 2. NEW: No self-credit of actual first-hit duplicate words

Module: `ResidualLossEarliestEdgePaymentSeparation.lean`.
Focused CI **38767513304 SUCCESS**, 3,317 jobs.
Both new `#print axioms` declarations have no `sorryAx`.

- `lossEarliestActualEdgeCarrier_subset_translatedLossAll`
- `lossEarliestActualEdgeCarrier_disjoint_outside_trueHoles`

For any genuine earliest-hit carrier E, global translated-loss
union U, and global true holes H = universe \\ original-covered:

```text
E ⊆ U,
E ∩ (H \\ U) = ∅.
```

Thus a debt word in E cannot ITSELF be counted as an outside
true-hole payment resource. **It might nevertheless be a true
hole *inside* U**; those inside-U holes were already cancelled
in the exact six-source external-hole frontier and may not be
credited again. These are statements about set membership, not
global debt payment.

## 3. NEW: Undoing the chosen loss flip is not a hole refund

Module: `ResidualLossEarliestEdgeFlipRefundObstruction.lean`.
Focused CI **38768459632 SUCCESS**, 3,318 jobs.
All three new `#print axioms` declarations have no `sorryAx`.

- `lossSlice_chosenFlip_is_covered`
- `lossEarliestActualEdgeCarrier_chosenFlip_is_covered`
- `lossEarliestActualEdgeCarrier_chosenFlip_not_trueHole`

For word x in the actual translated-loss slice T_c,

```text
flip_c(x) ∈ coveredCompletionWords(C),
flip_c(x) ∉ globalTrueHoles(C).
```

The same applies to first-occurrence real-edge carriers at c.
This rules out the *chosen-coordinate undo-flip* as the final
outside-hole refund. It does NOT prove that some other flip,
multi-flip or global matching cannot produce an outside hole.

## 4. NEW two-covered-ancestor target (pending independent certificate)

Module `ResidualLossCrossSliceTwoCoveredAncestors.lean` is
CERTIFIED: focused CI **38768731509 SUCCESS**, 3,319 jobs.
The theorem `lossEarliestActualEdgeCarrier_two_covered_ancestors`
has axioms `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

For any real source/blocker loss collision word x in two
distinct selected slices c and d:

```text
flip_c(x) ∈ coveredCompletionWords(C),
flip_d(x) ∈ coveredCompletionWords(C),
flip_c(x) ≠ flip_d(x).
```

Thus both immediate chosen-coordinate flips return to two
different COVERED original words, not to true holes. An alternative
matching or multi-coordinate construction is not ruled out.

## 5. Independent legacy compilation repairs

- `LocalZeroUnitStep.lean`,
  `NonExposedSupportThreeExactTransitions.lean`,
  `TriangleCriticalTransitionSeed.lean`: combined focused
  CI **38767901024 SUCCESS**, 3,463 jobs; Lean code repaired,
  no new admissions. Fixes were corrected list-cons
  membership, `AngleCap p lam` binder scope, and a tactic
  invoked after the goal was already closed.
- `SupportTwoZeroAngleAverage.lean`:
  focused CI **38768205395 SUCCESS**, 3,239 jobs.
  The induction uses existing certified
  `listPositiveCount_le_length` to justify natural-number
  truncated-subtraction arithmetic. `zeroAngleEntries_length`
  is audited without `sorryAx`.

The whole Fast Incremental Lean workflow was not green at
checkpoint. Run 38763344402 previously contained 409 error
diagnostics over 56 legacy modules. Later full runs may have
CI download failures/cancellations, so do not interpret a
network failure as newly discovered Lean failures.

## 6. Remaining mathematical requirement

An **external** injection, matching or independent cardinal
inequality is still needed to pay simultaneously:

```text
other-five genuine terminal debts
 + genuinely covered translated-loss blocker union
 + exact triple-index earliest retained-edge duplicate events
≤ genuine true holes OUTSIDE U
  + genuinely UNRESERVED dyadic surplus.
```

The exact carrier decomposition and edge-label uniqueness
give bookkeeping, NOT an injection from the debt-event tokens
into the globally eligible resources. Even if the two distinct
chosen-flip ancestors are covered, a different global
construction could still be possible. The needed matching or
geometry remains unproved.

This checkpoint records what has been *proved* and what has not,
without altering the admitted main WIP `sorry`.
