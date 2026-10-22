# JSP-000404 — unconditional n=4 equality same-sign gap checkpoint (2026-10-22)

Branch: `research/jsp-000404-sharp-centre`.
Status: **PARTIAL RESEARCH RESULT; NOT A PROOF OR DISPROOF OF JSP-000404**.

## Kernel-certified geometric reduction

Source: `JSP000404Research/SixPointNFourUnconditionalSameSignSlot.lean`.
Focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/39806826931
Result: **SUCCESS**, 3545 Lake jobs.

Both exported theorems' `#print axioms` consist of exactly
`[propext, Classical.choice, Quot.sound]`; neither includes `sorryAx`.

1. `six_point_n_four_equality_exists_global_sameSign_unit_slot`

   Under the **actual original six-centre** hypotheses, `n=4`,
   `0 ≤ delta < 1/2`, `t=4+delta`, `lam=pi/t`, genuine `AngleCap`,
   one top centre of exponent 3, all other five of exponent 1, and
   total `unitSupport=10`, there is a true dependent original-centre
   `GlobalUnitGapSlot C t` which is **same-sign**. No
   `ExactAngleWitness` assumption is needed.

   Proof composition:
   - `exists_strictlyExposed_ne_fixed` yields an exposed non-top
     original centre `j` from six distinct original points;
   - `six_point_n_four_unit_budget_equality_forces_11200` gives
     `unitSupport=2` and `positiveSupport=3` at `j`;
   - `one_sign_transition_of_strictlyExposed` produces one
     concrete sign transition on `(C j).rays`;
   - `six_point_n_four_one_transition_minimum_has_sameSign_slot`
     locates a genuine same-sign unit gap at that centre.

2. `six_point_n_four_equality_nonSameSign_slot_card_le_nine`

   Under the same geometric and equality premises, for **any**
   finite set `S : Finset (GlobalUnitGapSlot C t)` whose members
   all satisfy `¬ GlobalUnitGapSameSign C t u`, one has
   `S.card ≤ 9`. This stronger formulation does not require an
   undecidable `Finset.filter` expression in the theorem statement.

This is stronger than the earlier conditional
`SixPointNFourActualSameSignSlot.lean` branch: the new theorem
does **not** split by exact-angle-witness sign transitions and does
**not** require the existence of an exact angle witness.

## Verified repairs in this work session

The preceding focused failure was in
`ExactWitnessTransitionOccurrence.lean`; subsequent source repairs
advanced the dependency gate through
`ExactWitnessSupportThreeTransition.lean` to
`SixPointNFourExactWitness.lean`. These are **not** thereby
certified globally; their current focused workflow status must be
checked independently.

Additional targeted repairs were committed for
`ResidualLocalSaturation`, `SixPointHardSupportReduction`,
`SixPointNFourNoCover`, `ExactWitnessDeficitTwo`,
`MixedSupportThreeMultiplicity`,
`SixPointMixedSupportTransitionBudget`, and
`CentreAdjacentTransitionOccurrence`.
Only independently passing focused or incremental results warrant a
kernel-certified label.

## What is not proved

- A unit-gap **location** is not a free Boolean true hole.
- A same-sign unit gap cannot be charged to a transition-only
  obstruction, but the necessary **actual global phase-cover**
  hypotheses have not been unconditionally proved from AngleCap.
- The root theorem in
  `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`
  still has one intentionally executable `sorry` and retains
  `sorryAx`.
- The general all-cardinality global non-reusing six-source payment,
  including true Boolean holes, hard/soft/mixed carriers, twin and
  duplicate fibre debt, projected loss, and net surplus reservations,
  remains open.
- A passing focused module is **not** a passing all-tree
  `JSP000404Research` build, nor full submission/award acceptance.

## Next mathematical bridge

From the certified nine-slot fact, one can exclude a complete
**transition-only** ten-slot cover whenever the actual covering
and phase lower-bound conditions are proved. The missing task is
to establish such a cover directly from genuine AngleCap geometry,
or find a valid alternative global payment mechanism. For higher
cardinalities, the global six-source non-reuse deficit remains the
separate main obstacle.
