import JSP000404Research.ResidualHardRemainder
import JSP000404Research.ResidualProjectionAccounting
import Mathlib.Tactic

/-!
# Exact hard-remainder payment with UNUSED strict-overlap surplus

The older sufficient criterion
    saturatedOverlap + loss <= holes
throws away profile surplus that was not used to pay strict--strict overlap.

Here:
  S = total dyadic projected profile surplus;
  O_ss = number of strict--strict overlap words;
  R = S - O_ss >= 0, the *unspent* surplus credit;
  H = 2^n - covered, the number of ambient Boolean holes;
  O_hard = saturated overlap words;
  L = total dyadic projected profile loss.

The exact global identity is:
    targetWeight + R + H = 2^n + O_hard + L.

Consequently the sharp target bound is EXACTLY equivalent to
    O_hard + L <= H + R.

This is a sharper and mathematically equivalent global payment criterion,
not merely the earlier overstrong sufficient condition O_hard+L<=H.

The proof is counting and works for arbitrary ordered edge colourings.
It does not establish the still-open geometric payment inequality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

/-- Strict--strict overlap never spends more than the total available
profile surplus; hence residual credit is genuine nonnegative mass. -/
theorem strictStrictOverlap_card_le_available_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) :
    (strictStrictOverlapWords C k).card ≤
      totalDyadicProfileSurplus k (projectedFree C) :=
  strictStrictOverlap_card_le_total_surplus C k

/-- The exact global accounting after paying only the strict--strict
overlaps, without discarding unused surplus. -/
theorem exact_hard_remainder_completion_balance
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) :
    (∑ v : V, 2 ^ k v) +
        (totalDyadicProfileSurplus k (projectedFree C) -
          (strictStrictOverlapWords C k).card) +
        (2 ^ n - (coveredCompletionWords C).card)
      =
      2 ^ n +
        (saturatedOverlapWords C k).card +
        totalDyadicProfileLoss k (projectedFree C) := by
  have hbalance :=
    residual_projection_accounting_balance
      k (projectedFree C)
      (coveredCompletionWords C).card
      (overlapCompletionWords C).card
      (projectedFree_mass_eq_covered_add_overlap C)
  have hcovered : (coveredCompletionWords C).card ≤ 2 ^ n :=
    coveredCompletionWords_card_le_two_pow C
  have hstrict :
      (strictStrictOverlapWords C k).card ≤
        totalDyadicProfileSurplus k (projectedFree C) :=
    strictStrictOverlap_card_le_available_surplus C k
  have hsplit :=
    saturatedOverlap_card_add_strict_eq_overlap C k
  omega

/-- The hard remainder is payable iff the original weighted dyadic
capacity holds: no false subset-wise Hall G1, and no discarded surplus. -/
theorem dyadic_capacity_iff_exact_hard_remainder_payment
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) :
    ((∑ v : V, 2 ^ k v) ≤ 2 ^ n) ↔
      ((saturatedOverlapWords C k).card +
          totalDyadicProfileLoss k (projectedFree C) ≤
        (2 ^ n - (coveredCompletionWords C).card) +
          (totalDyadicProfileSurplus k (projectedFree C) -
            (strictStrictOverlapWords C k).card)) := by
  have hbalance := exact_hard_remainder_completion_balance C k
  omega

/-- Any genuine overweight counterexample exhibits a strict non-payable
*hard* defect even after all unused profile surplus is retained. -/
theorem overweight_forces_unpaid_exact_hard_remainder
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ)
    (hover : 2 ^ n < ∑ v : V, 2 ^ k v) :
    (2 ^ n - (coveredCompletionWords C).card) +
        (totalDyadicProfileSurplus k (projectedFree C) -
          (strictStrictOverlapWords C k).card)
      <
      (saturatedOverlapWords C k).card +
        totalDyadicProfileLoss k (projectedFree C) := by
  have hbalance := exact_hard_remainder_completion_balance C k
  omega

#print axioms strictStrictOverlap_card_le_available_surplus
#print axioms exact_hard_remainder_completion_balance
#print axioms dyadic_capacity_iff_exact_hard_remainder_payment
#print axioms overweight_forces_unpaid_exact_hard_remainder

end OrderedEdgeColoring
end JSP000404Research
