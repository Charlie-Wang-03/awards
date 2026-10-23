# JSP-000404 — All-Positive-Gap and Common-Safe-Cut Checkpoint (2026-10-23)

## Scope and hard boundary

Repository: `Charlie-Wang-03/awards`; research branch:
`research/jsp-000404-sharp-centre`.

**The original JSP-000404 is NOT proved or disproved.**
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` still contains
its one genuine executable `sorry`, for a GLOBAL, original-geometry,
non-reusing allocation of TRUE Boolean holes and genuinely unreserved
dyadic surplus paying all hard/soft/twin/mixed-rigid/mobile NET collision
and projected-loss debts. Do not substitute covered words or merely
candidate slot counts for true holes. Do not introduce an axiom.

The full Lean research-module tree still fails to compile: e.g. before the
present focused repairs run 39934702612 reported 129 errors in 11 modules.
This count is an historical CI snapshot, not a claimed current tally.

## New kernel-verified geometry

1. **Common safe cut, six centres, n >= 5.**
   `SixPointSafeCutSignUniformity.lean`:
   `six_point_exists_common_cut_short_band_sign_uniform`.
   It proves that one and the SAME original projective cut makes the
   cut-adjusted signs of ALL rays in the [0,1+delta] normalized short band
   agree centrewise. The band may be empty. No payment follows.
   Run [39938092436](https://github.com/Charlie-Wang-03/awards/actions/runs/39938092436):
   success, 9076 Lake jobs, printed axioms without `sorryAx`.

2. **Full cyclic positive-gap interval bridge, all q >= 1.**
   `PositiveGapPhaseInterval.lean`,
   `CutTransitionSeedCriticalSlot.lean`, and `BoundaryCutShift.lean`
   were repaired and built together.
   `GlobalCyclicPositiveGapBadAt` implies the same slot's periodic
   delta-arc. Its exact bad interval is of width `q+delta-s`,
   `q=floor(s)`, <= delta. The cut transition and boundary shift
   are original-geometry local bridges.
   Run [39939179977](https://github.com/Charlie-Wang-03/awards/actions/runs/39939179977):
   success, 9078 Lake jobs, audited core theorems without `sorryAx`.

3. **SEVENTEEN cyclic phase sample certificate covering all q >= 1.**
   `PositiveGapSeventeenPhase.lean`:
   `six_point_exists_unblocked_positiveGap_seventeenPhase` and
   `six_point_exists_period_phase_without_positiveGap_bad`.
   In the six-centre top-(n-1) / five-(n-3) profile, n >= 8,
   0 <= delta < 1/2 and t=n+delta, all positive quotient-gap slots
   total at most sixteen. Seventeen equally spaced physical-circle
   samples have direct/complementary separations larger than delta
   because 17*delta < t. One in-period phase thus avoids every
   canonical q>=1 periodic positive-gap bad interval.
   Run [39939180003](https://github.com/Charlie-Wang-03/awards/actions/runs/39939180003):
   success, 9077 Lake jobs, printed axioms without `sorryAx`.
   **This does NOT prove that dyadic-payment failure produces such a
   bad-gap certificate, so no global theorem is closed.**

4. **Separated support-two witness, uncompensated top deletion.**
   `SixPointSeparatedSupportTwo.lean`:
   `five_survivor_weight_ge_six_point_profile_of_at_least_four_gains`,
   `topDeletionGainMinima_card_le_three_of_no_compensated_top` and
   `exists_separated_support_two_minimum_of_no_compensated_top`.
   A six-centre top deletion lacking four compensated minima forces
   a non-top, non-gaining minimum with exactly two positive quotient
   positions, and no top-pinned positive-positive pair.
   Run [39939619350](https://github.com/Charlie-Wang-03/awards/actions/runs/39939619350):
   success, 3550 Lake jobs, printed axioms without `sorryAx`.
   This is a local structural necessary condition, NOT a proof of
   incompatibility with AngleCap.

All above first three independent kernel-proved chains are imported into
the research umbrella `JSP000404Research.lean` where applicable.
A green *focused* check does not certify the whole umbrella build.

## Pending source repair (do not claim green until checked)

`ExactWitnessUnitGapMass.lean` formerly made a recursive call on
`W.swapEnds`, violating Lean structural termination. It has been
factored into an ordered helper and a nonrecursive swapped-witness
dispatcher, and has received several dependent-list and conjunction
transport repairs. Its final focused check must be read before marking
this module accepted:

[39940197572](https://github.com/Charlie-Wang-03/awards/actions/runs/39940197572).

No further executable `sorry` has been added to the branch.

## Next actual mathematical frontier

1. Prove an ORIGINAL-geometry implication: a hypothetical failure of
   the true global non-reusing dyadic / outside-translated-loss Boolean
   hole payment forces sufficiently many concrete cut-adjacent or
   canonical q-positive periodic bad-gap certificates. The known
   avoidance results alone cannot establish this direction.
2. Establish a global source-to-reserved-resource injection or
   capacity matching accounting across distinct targets/bridges,
   explicitly charging fifth-centre-covered diagonals, twins,
   mixed-rigid carriers, soft blockers, cross-coordinate duplicates,
   and projected loss. Candidate sinks / SOFT words are covered,
   not TRUE holes. No double-counting of physical holes or
   already-reserved surplus is allowed.
3. Repair remaining whole-tree Lean errors independently and audit
   the original theorem's entire dependency closure for `sorryAx`.
