import JSP000404Research.ZeroMinimumOverweightArithmetic
import JSP000404Research.ResidualHardRemainder
import JSP000404Research.PlanarLowerBranchHardWordInjection
import Mathlib.Tactic

/-!
# Exact residual defect in a zero-minimum minimal overweight step

If the target dyadic mass is exactly one above the sharp bound,

  targetMass = 2^n + 1,

then the exact residual projection accounting identity gives

  overlap + profileLoss
    = holes + profileSurplus + 1.

Thus a minimal overweight counterexample with a zero minimum has exactly one
unit of net unpaid residual defect.

After splitting overlap into strict--strict words and the saturated remainder,
and using that strict--strict overlap is bounded by total profile surplus, the
concrete hard demand satisfies

  saturatedOverlap + lossWords >= holes + 1.

This turns the final lower-branch obstruction into an equality-rigidity
problem: any extra unit of available payment beyond the already-accounted
credits kills the minimal counterexample.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

theorem residual_net_defect_eq_one_of_target_eq_bound_add_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1) :
    (overlapCompletionWords C).card +
        totalDyadicProfileLoss exponent (projectedFree C)
      =
    (2 ^ n - (coveredCompletionWords C).card) +
        totalDyadicProfileSurplus exponent (projectedFree C) + 1 := by
  have hcovered :
      (coveredCompletionWords C).card ≤ 2 ^ n :=
    coveredCompletionWords_card_le_two_pow C
  have hproject0 :=
    projectedFree_mass_eq_covered_add_overlap C
  have hproject :
      (∑ v, 2 ^ projectedFree C v) =
        (coveredCompletionWords C).card +
          (overlapCompletionWords C).card := by
    simpa [projectedFree] using hproject0
  have hbalance :=
    residual_projection_accounting_balance
      exponent (projectedFree C)
      (coveredCompletionWords C).card
      (overlapCompletionWords C).card
      hproject
  rw [htarget] at hbalance
  omega

/-- Exact-one overweight forces the concrete hard remainder to exceed the
global Boolean-hole count by at least one. -/
theorem holes_add_one_le_saturatedOverlap_add_profileLoss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1) :
    (2 ^ n - (coveredCompletionWords C).card) + 1
      ≤
    (saturatedOverlapWords C exponent).card +
      totalDyadicProfileLoss exponent (projectedFree C) := by
  have hnet :=
    residual_net_defect_eq_one_of_target_eq_bound_add_one
      C exponent htarget
  have hsplit :=
    saturatedOverlap_card_add_strict_eq_overlap
      C exponent
  have hstrict :=
    strictStrictOverlap_card_le_total_surplus
      C exponent
  omega

/-- Under the standard one-layer hypothesis, the same rigidity is expressed by
the concrete finite loss-word set. -/
theorem holes_add_one_le_hardProjectionWords_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1) :
    (projectionHoleWords C).card + 1 ≤
      (hardProjectionWords C exponent).card := by
  rw [projectionHoleWords_card C,
      hardProjectionWords_card_eq C exponent hexp honeLoss]
  rw [lossCompletionWords_card_eq_totalDyadicProfileLoss
      C exponent hexp honeLoss]
  exact holes_add_one_le_saturatedOverlap_add_profileLoss
    C exponent htarget

/-- A zero-minimum minimal-overweight step therefore has exact net residual
defect one and a hard-word set strictly larger than the hole set. -/
theorem zero_minimum_child_bound_forces_unit_hard_defect
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (r : V)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hmonoR :
      ∀ i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ v : V, 2 ^ exponent v)
    (hchildR :
      deletionPostWeight after r ≤ 2 ^ n)
    (hrZero : exponent r = 0) :
    (overlapCompletionWords C).card +
          totalDyadicProfileLoss exponent (projectedFree C)
        =
      (2 ^ n - (coveredCompletionWords C).card) +
          totalDyadicProfileSurplus exponent (projectedFree C) + 1
    ∧
    (projectionHoleWords C).card + 1 ≤
      (hardProjectionWords C exponent).card := by
  have htarget :=
    zero_minimum_overweight_excess_eq_one_of_child_bound_arith
      exponent after n r hexp hmonoR hover hchildR hrZero
  exact ⟨
    residual_net_defect_eq_one_of_target_eq_bound_add_one
      C exponent htarget,
    holes_add_one_le_hardProjectionWords_card
      C exponent hexp honeLoss htarget⟩

#print axioms residual_net_defect_eq_one_of_target_eq_bound_add_one
#print axioms holes_add_one_le_saturatedOverlap_add_profileLoss
#print axioms holes_add_one_le_hardProjectionWords_card
#print axioms zero_minimum_child_bound_forces_unit_hard_defect

end OrderedEdgeColoring
end JSP000404Research
