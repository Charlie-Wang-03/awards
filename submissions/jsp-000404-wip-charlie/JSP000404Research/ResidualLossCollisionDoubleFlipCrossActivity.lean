import JSP000404Research.ResidualLossEarliestEdgeTwoOwnerCorners
import JSP000404Research.ResidualLossExternalHoleBudget
import Mathlib.Tactic

/-!
# Exact necessary cross-activity for the ONLY possible two-flip local refund

A genuine first-hit translated-loss collision word `w` is carried by two
DIFFERENT original retained cube owners v,wowner, with selected flip
coordinates c,d. The two immediate ancestors `flip(w,c)` and `flip(w,d)`
are covered by these respective owners.

The only other Boolean vertex in their two-coordinate Hamming square is
`q=flip(flip(w,c),d)`. For q to be a GENUINE TRUE Boolean hole,
the OPPOSITE coordinate d must be active at v, and c must be active
at wowner. Otherwise the corresponding original owner's completion cube
also covers q. Neither source is allowed to pay an alleged hole by an
inactive-coordinate flip.

This is a NEW unconditional NECESSARY geometrically meaningful
cross-activity obstruction; it does not assert either cross-activity
or that q is actually a globally uncovered/externally eligible hole.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- If the opposite two-bit corner is a genuine GLOBAL hole, the
two distinct original collision endpoints must be cross-active at
the OTHER endpoint's chosen coordinate. -/
theorem actual_loss_collision_double_flip_true_hole_forces_cross_activity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d : Fin n} (hcd : c ≠ d)
    (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d)
    {word : Fin n → Bool}
    (hw : word ∈ lossEarliestActualEdgeCarrier
      C exponent choice c d p)
    (htrue :
      flipBoolWordAt (flipBoolWordAt word c) d ∈
        lossLedgerGlobalTrueHoles C) :
    d ∈ retainedActive C p.1 ∧ c ∈ retainedActive C p.2 := by
  classical
  obtain ⟨_, hvSource, hwSource, _⟩ :=
    lossEarliestActualEdgeCarrier_two_distinct_owner_ancestors
      C exponent choice hcd p hp hw
  let q := flipBoolWordAt (flipBoolWordAt word c) d
  have hqNotCovered : q ∉ coveredCompletionWords C :=
    (Finset.mem_sdiff.mp htrue).2
  constructor
  · by_contra hdInactive
    have hqOwner : q ∈ retainedCompletionWords C p.1 := by
      exact (mem_retainedCompletionWords_flip_iff_of_inactive
        C hdInactive).2 hvSource
    have hqCovered : q ∈ coveredCompletionWords C :=
      (mem_coveredCompletionWords C q).2
        ⟨p.1, (mem_completionFibre C q p.1).2 hqOwner⟩
    exact hqNotCovered hqCovered
  · by_contra hcInactive
    have hqOwner' :
        flipBoolWordAt (flipBoolWordAt word d) c ∈
          retainedCompletionWords C p.2 :=
      (mem_retainedCompletionWords_flip_iff_of_inactive
        C hcInactive).2 hwSource
    have hqOwner : q ∈ retainedCompletionWords C p.2 := by
      simpa only [q, flipBoolWordAt_commute word hcd] using hqOwner'
    have hqCovered : q ∈ coveredCompletionWords C :=
      (mem_coveredCompletionWords C q).2
        ⟨p.2, (mem_completionFibre C q p.2).2 hqOwner⟩
    exact hqNotCovered hqCovered

/-- In particular the double-flip corner cannot be a payable
TRUE hole OUTSIDE translated losses unless both cross-activities hold.
Even when they do hold, a THIRD-PARTY cube or another loss slice may
still disqualify the target. -/
theorem actual_loss_collision_double_flip_external_hole_forces_cross_activity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d : Fin n} (hcd : c ≠ d)
    (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d)
    {word : Fin n → Bool}
    (hw : word ∈ lossEarliestActualEdgeCarrier
      C exponent choice c d p)
    (htrue :
      flipBoolWordAt (flipBoolWordAt word c) d ∈
        lossLedgerOutsideTranslatedTrueHoles C exponent choice) :
    d ∈ retainedActive C p.1 ∧ c ∈ retainedActive C p.2 := by
  exact actual_loss_collision_double_flip_true_hole_forces_cross_activity
    C exponent choice hcd p hp hw
      (Finset.mem_sdiff.mp htrue).1

#print axioms actual_loss_collision_double_flip_true_hole_forces_cross_activity
#print axioms actual_loss_collision_double_flip_external_hole_forces_cross_activity

end OrderedEdgeColoring
end JSP000404Research
