import JSP000404Research.MinimalOverweightResidualDefect
import Mathlib.Tactic

/-!
# Refined hard remainder: retain unused strict-overlap surplus

ResidualHardRemainder pays strict--strict overlap from total profile surplus
and then discards any surplus left over.  That is stronger than necessary.

Let

  Q = card(strictStrictOverlapWords),
  S = totalDyadicProfileSurplus.

Since Q <= S, after paying the strict--strict overlap there remain exactly

  S - Q

units of profile surplus.  The exact master condition is therefore

  saturatedOverlap + profileLoss
    <= holes + (S - Q).

This is equivalent to the original residual defect payment

  overlap + profileLoss <= holes + S,

because

  overlap = saturatedOverlap + Q.

Under the one-layer hypothesis the profile loss is the concrete cardinality of
lossCompletionWords, giving a refined hard-word outlet which preserves every
available unit of surplus.

In a zero-minimum minimal overweight counterexample, exact residual accounting
then forces

  hardDemand = holes + remainingSurplus + 1.

Thus after all already-proved credits are retained, the genuine global
augmenting deficiency is exactly one.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

def remainingStrictPaymentSurplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : ℕ :=
  totalDyadicProfileSurplus exponent (projectedFree C) -
    (strictStrictOverlapWords C exponent).card

theorem strictStrict_add_remainingSurplus_eq_totalSurplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (strictStrictOverlapWords C exponent).card +
        remainingStrictPaymentSurplus C exponent
      =
    totalDyadicProfileSurplus exponent (projectedFree C) := by
  unfold remainingStrictPaymentSurplus
  have hle :=
    strictStrictOverlap_card_le_total_surplus C exponent
  omega

/-- Sharp hard-remainder outlet retaining the profile surplus not spent on
strict--strict overlap. -/
theorem exponent_capacity_of_refined_hard_payment
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hpay :
      (saturatedOverlapWords C exponent).card +
          totalDyadicProfileLoss exponent (projectedFree C)
        ≤
      (2 ^ n - (coveredCompletionWords C).card) +
          remainingStrictPaymentSurplus C exponent) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  apply exponent_capacity_of_completion_defect_payment
    C exponent
  have hsplit :=
    saturatedOverlap_card_add_strict_eq_overlap C exponent
  have hremain :=
    strictStrict_add_remainingSurplus_eq_totalSurplus
      C exponent
  omega

/-- Concrete one-layer version. -/
theorem exponent_capacity_of_refined_hard_words_payment
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hpay :
      (hardProjectionWords C exponent).card
        ≤
      (projectionHoleWords C).card +
        remainingStrictPaymentSurplus C exponent) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  rw [hardProjectionWords_card_eq
      C exponent hexp honeLoss] at hpay
  rw [projectionHoleWords_card C] at hpay
  rw [lossCompletionWords_card_eq_totalDyadicProfileLoss
      C exponent hexp honeLoss] at hpay
  exact exponent_capacity_of_refined_hard_payment
    C exponent hpay

/-- Exact hard-demand identity at target mass 2^n+1.  The refined global
deficiency is exactly one. -/
theorem hardProjectionWords_card_eq_holes_add_remainingSurplus_add_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1) :
    (hardProjectionWords C exponent).card
      =
    (projectionHoleWords C).card +
      remainingStrictPaymentSurplus C exponent + 1 := by
  have hnet :=
    residual_net_defect_eq_one_of_target_eq_bound_add_one
      C exponent htarget
  have hsplit :=
    saturatedOverlap_card_add_strict_eq_overlap
      C exponent
  have hremain :=
    strictStrict_add_remainingSurplus_eq_totalSurplus
      C exponent
  have hloss :=
    lossCompletionWords_card_eq_totalDyadicProfileLoss
      C exponent hexp honeLoss
  rw [hardProjectionWords_card_eq C exponent hexp honeLoss,
      projectionHoleWords_card C,
      hloss]
  omega

/-- Zero-minimum minimal overweight specialization: after all strict-overlap
surplus is retained, exactly one hard unit remains unmatched. -/
theorem zero_minimum_child_bound_refined_deficiency_eq_one
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
    (hardProjectionWords C exponent).card
      =
    (projectionHoleWords C).card +
      remainingStrictPaymentSurplus C exponent + 1 := by
  have htarget :=
    zero_minimum_overweight_excess_eq_one_of_child_bound
      exponent after n r hexp hmonoR hover hchildR hrZero
  exact
    hardProjectionWords_card_eq_holes_add_remainingSurplus_add_one
      C exponent hexp honeLoss htarget

#print axioms strictStrict_add_remainingSurplus_eq_totalSurplus
#print axioms exponent_capacity_of_refined_hard_payment
#print axioms exponent_capacity_of_refined_hard_words_payment
#print axioms hardProjectionWords_card_eq_holes_add_remainingSurplus_add_one
#print axioms zero_minimum_child_bound_refined_deficiency_eq_one

end OrderedEdgeColoring
end JSP000404Research
