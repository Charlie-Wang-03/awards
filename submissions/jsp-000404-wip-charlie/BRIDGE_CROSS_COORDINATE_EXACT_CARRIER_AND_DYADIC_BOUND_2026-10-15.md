# JSP-000404 — Exact cross-coordinate loss carriers and dyadic bounds (2026-10-15)

Branch: `research/jsp-000404-sharp-centre`.
Status: research only; the original conjecture has not been proved or disproved.
The sole executable `sorry` in `PlanarLowerBranchProofAdmittedWIP.lean`
remains unmodified and must not be hidden, relocated, or counted as closed.

## I. Certified actual-edge orientation

Module: `ResidualLossActualEdgeCarrierFrontier.lean`.
Commit: `acfa40b43a4b8acc3350489848b948df9064968c`.
Focused CI **38739815915: SUCCESS**. Both new theorems'
`#print axioms` output has NO `sorryAx`:

- `chosenLossActualEdgeBlockerTriples_orientation`
- `chosenLossActualEdgeBlockerTriples_side_of_bit`

For every actual source/blocker triple with chosen coordinate `choice v`,
the original canonical retained bit determines the side **exactly**:
`retainedBit C v (choice v) = true` forces `w < v`, while
`= false` forces `v < w`. This strengthens the earlier no-straddle
and one-sidedness results but does not imply single-neighbour uniqueness
or global Boolean word payment.

## II. Certified exact pair partition of cross-coordinate conflicts

Module: `ResidualLossCrossSliceCarrier.lean`.
Repair commit: `2a1a71b4fd5ff4349f24936f3bfcd8312fe641be`.
Focused CI **38740700053: SUCCESS**, 3,307 build jobs, no `sorryAx`.

Certified theorems:

- `crossLossPairWords_pairwiseDisjoint`
- `crossTranslatedLossSlice_inter_eq_biUnion_pairs`
- `crossTranslatedLossSlice_inter_card_eq_sum_pairs`
- `crossLossConflictPair_edge_colour`

For **fixed distinct coordinates** c != d, define `T_c` as the
translated loss slice and `P_cd` as pairs of loss owners whose
translated cubes intersect. Then

```text
|T_c ∩ T_d|
  = Σ_(p ∈ P_cd) |translatedCube(p.1,c) ∩ translatedCube(p.2,d)|
```

because the pair-carrier intersections are pairwise disjoint
**within that one fixed ordered coordinate pair**. Each pair in
`P_cd` corresponds to a genuine retained edge whose colour is
either c or d. No disjointness across DIFFERENT coordinate pairs
is asserted or used.

The sorry-free umbrella `VerifiedOverlapRewire.lean` now imports
the certified exact pair-carrier module (commit
`efafa6e33b75a220ba5fd53e58fa660c640c784c`). Its separate
focused root CI **38741412715** must be checked independently;
a successful isolated carrier check is not a root-build success.

## III. Certified quantitative per-pair dyadic envelope

New theorem commit:
`fd88093323a42eae3ea8d91309e9e2e3018f235d`.
Focused CI **38741614008: SUCCESS**, 3,307 build jobs, no `sorryAx`.

New theorems:

- `crossLossPairWords_card_le_min_dyadic`
- `crossTranslatedLossSlice_inter_card_le_sum_min_dyadic`

They prove the explicit **upper** bound

```text
|T_c ∩ T_d|
  <= Σ_(p ∈ P_cd) min(2^projectedFree(p.1), 2^projectedFree(p.2)).
```

Only true intersecting translated cubes are counted. The bound
does NOT manufacture outside true holes, claim independence between
coordinate pairs, or cancel any already reserved surplus.

## IV. Additional legacy Lean repair

`TransitionQuotientOccurrence.lean`:
commit `b3d4056edea39db3d6fa6046de36c66999009463`,
focused CI **38741131541: SUCCESS**, 3,225 build jobs.
The three checked theorems
`raySignAt_eq_of_rayThetaAt_eq`,
`transitionQuotientOccurs_two_blocks_iff`, and
`unique_transition_quotient_eq_of_occurs` have no `sorryAx`.
Fixes include the AngleCap binder, outdated list-length API,
and inductive impossible-transition case.

## V. Honest remaining mathematical boundary

For active loss choices, the exact original terminal frontier remains

```text
terminalTwinOtherFiveDebt
  + |actual same-colour retained-edge covered blocker union|
  + translatedLossDuplicateDebt
<= |true holes outside translated loss union|
  + terminalTwinAvailableSurplus.
```

The present certified identities handle individual `T_c∩T_d`.
They do NOT bound the global duplicate debt by a sum of those
intersections in Lean, nor prove a globally non-reusing allocation.

A mathematically natural, STILL UNFORMALIZED intermediate inequality is

```text
D_dup = Σ_c |T_c| - |⋃_c T_c|
   <= Σ_(c<d) |T_c ∩ T_d|
   <= Σ_(c<d) Σ_(p∈P_cd) min(2^free(p.1),2^free(p.2)).
```

The first inequality is a finite-family union-overcount bound and
must be established in the pinned Lean environment, NOT treated as
a certified theorem by this document. Even after it is proved,
its right-hand side must still be globally paid together with the
five other debt classes using strictly non-reused true holes and
genuinely unreserved surplus. The last admitted `sorry` is open.

Full Fast Incremental Lean CI was historically non-green due to many
legacy modules; focused green checks do not imply full-workspace success.
