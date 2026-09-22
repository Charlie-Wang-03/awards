
import JSP000404Research.ResidualStrictOverlapPayment
import JSP000404Research.ResidualLossWords
import JSP000404Research.ResidualCompletionAccounting
import Mathlib.Tactic

/-!
# Final residual reduction to hard bad words versus Boolean holes

Strict--strict overlap words are globally paid by profile surplus.  Remove
them from the global overlap set and call the remainder saturatedOverlapWords.

The other cost in the projection accounting is lossCompletionWords.  These are
disjoint from every overlap word.

Define

  hardProjectionWords
    = lossCompletionWords union saturatedOverlapWords.

Then the following single condition is sufficient for the sharp capacity:

  card(hardProjectionWords)
    <= 2^n - card(coveredCompletionWords).

In words: after strict--strict overlaps are paid by profile surplus, it is
enough to inject every remaining hard bad word into an uncovered retained
Boolean word.

This is a concrete finite matching target for the residual blocker/free-hole
machinery.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

theorem strictResidualActiveSlices_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Disjoint
      (strictResidualActiveSlice C exponent false)
      (strictResidualActiveSlice C exponent true) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvF hvT
  have hF :=
    ((mem_strictResidualActiveSlice
      C exponent false v).1 hvF).1
  have hT :=
    ((mem_strictResidualActiveSlice
      C exponent true v).1 hvT).1
  have hFb := (mem_residualActiveSlice C false v).1 hF
  have hTb := (mem_residualActiveSlice C true v).1 hT
  rw [hFb.2] at hTb
  simp at hTb

/-- The surplus used to pay strict--strict overlaps is a sub-sum of the full
profile surplus, so there is no hidden double counting. -/
theorem strictSliceSurplus_le_totalSurplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    strictResidualSliceSurplus C exponent false +
        strictResidualSliceSurplus C exponent true
      ≤
    totalDyadicProfileSurplus exponent (projectedFree C) := by
  classical
  let A := strictResidualActiveSlice C exponent false
  let B := strictResidualActiveSlice C exponent true
  let f : V → ℕ :=
    dyadicProfileSurplus exponent (projectedFree C)
  have hdisj : Disjoint A B := by
    exact strictResidualActiveSlices_disjoint C exponent
  have hsumUnion :
      (∑ v ∈ A, f v) + (∑ v ∈ B, f v) =
        ∑ v ∈ A ∪ B, f v := by
    rw [Finset.sum_union hdisj]
  have hsub :
      A ∪ B ⊆ (Finset.univ : Finset V) :=
    Finset.subset_univ _
  have hle :
      (∑ v ∈ A ∪ B, f v) ≤
        ∑ v : V, f v :=
    Finset.sum_le_sum_of_subset hsub
  unfold strictResidualSliceSurplus totalDyadicProfileSurplus
  change
    (∑ v ∈ A, f v) + (∑ v ∈ B, f v) ≤
      ∑ v : V, f v
  rw [hsumUnion]
  exact hle

/-- The overlap set splits exactly into the payable strict--strict part and
the remaining saturated part. -/
theorem overlap_card_eq_strict_add_saturated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (overlapCompletionWords C).card =
      (strictStrictOverlapWords C exponent).card +
        (saturatedOverlapWords C exponent).card := by
  classical
  have hsub :=
    strictStrictOverlap_subset_overlapCompletionWords
      C exponent
  have hsat :
      (saturatedOverlapWords C exponent).card =
        (overlapCompletionWords C).card -
          (strictStrictOverlapWords C exponent).card := by
    unfold saturatedOverlapWords
    rw [Finset.card_sdiff_of_subset hsub]
  have hle :
      (strictStrictOverlapWords C exponent).card ≤
        (overlapCompletionWords C).card :=
    Finset.card_le_card hsub
  omega

noncomputable def hardProjectionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Finset (Fin n → Bool) :=
  lossCompletionWords C exponent ∪
    saturatedOverlapWords C exponent

/-- Loss words and saturated-overlap words are disjoint. -/
theorem lossWords_disjoint_saturatedOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1) :
    Disjoint
      (lossCompletionWords C exponent)
      (saturatedOverlapWords C exponent) := by
  classical
  apply Finset.disjoint_of_subset_right
    (Finset.sdiff_subset)
  exact lossCompletionWords_disjoint_overlapCompletionWords
    C exponent hexp honeLoss

theorem hardProjectionWords_card_eq
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (hardProjectionWords C exponent).card =
      totalDyadicProfileLoss exponent (projectedFree C) +
        (saturatedOverlapWords C exponent).card := by
  unfold hardProjectionWords
  rw [Finset.card_union_of_disjoint
      (lossWords_disjoint_saturatedOverlapWords
        C exponent hexp honeLoss),
      lossCompletionWords_card_eq_totalDyadicProfileLoss
        C exponent hexp honeLoss]

/-- Main reduced outlet: hard bad words fitting into the Boolean holes closes
the complete target dyadic capacity. -/
theorem exponent_capacity_of_hardWords_le_holes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hhard :
      (hardProjectionWords C exponent).card ≤
        2 ^ n - (coveredCompletionWords C).card) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  have hhard' :
      totalDyadicProfileLoss exponent (projectedFree C) +
          (saturatedOverlapWords C exponent).card
        ≤
      2 ^ n - (coveredCompletionWords C).card := by
    rw [← hardProjectionWords_card_eq
      C exponent hexp honeLoss]
    exact hhard
  have hstrict :=
    strictStrictOverlap_card_le_slice_surplus
      C exponent
  have hstrictTotal :=
    strictSliceSurplus_le_totalSurplus
      C exponent
  have hoverlap :=
    overlap_card_eq_strict_add_saturated
      C exponent
  have hpay :
      (overlapCompletionWords C).card +
          totalDyadicProfileLoss exponent (projectedFree C)
        ≤
      (2 ^ n - (coveredCompletionWords C).card) +
          totalDyadicProfileSurplus exponent (projectedFree C) := by
    omega
  exact exponent_capacity_of_completion_defect_payment
    C exponent hpay


def strictSliceSurplusTotal
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : ℕ :=
  strictResidualSliceSurplus C exponent false +
    strictResidualSliceSurplus C exponent true

def remainingProfileSurplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : ℕ :=
  totalDyadicProfileSurplus exponent (projectedFree C) -
    strictSliceSurplusTotal C exponent

theorem strict_add_remainingProfileSurplus_eq_total
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    strictSliceSurplusTotal C exponent +
        remainingProfileSurplus C exponent =
      totalDyadicProfileSurplus exponent (projectedFree C) := by
  unfold strictSliceSurplusTotal remainingProfileSurplus
  have hle :=
    strictSliceSurplus_le_totalSurplus C exponent
  omega

/-- Weaker and more natural final outlet: hard bad words may be paid jointly
by uncovered Boolean words and all profile surplus not reserved for the
strict--strict overlap payment. -/
theorem exponent_capacity_of_hardWords_le_holes_add_remainingSurplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hhard :
      (hardProjectionWords C exponent).card ≤
        (2 ^ n - (coveredCompletionWords C).card) +
          remainingProfileSurplus C exponent) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  have hhard' :
      totalDyadicProfileLoss exponent (projectedFree C) +
          (saturatedOverlapWords C exponent).card
        ≤
      (2 ^ n - (coveredCompletionWords C).card) +
        remainingProfileSurplus C exponent := by
    rw [← hardProjectionWords_card_eq
      C exponent hexp honeLoss]
    exact hhard
  have hstrict :=
    strictStrictOverlap_card_le_slice_surplus
      C exponent
  have hoverlap :=
    overlap_card_eq_strict_add_saturated
      C exponent
  have hsplit :=
    strict_add_remainingProfileSurplus_eq_total
      C exponent
  unfold strictSliceSurplusTotal at hsplit
  have hpay :
      (overlapCompletionWords C).card +
          totalDyadicProfileLoss exponent (projectedFree C)
        ≤
      (2 ^ n - (coveredCompletionWords C).card) +
          totalDyadicProfileSurplus exponent (projectedFree C) := by
    omega
  exact exponent_capacity_of_completion_defect_payment
    C exponent hpay

#print axioms strictSliceSurplus_le_totalSurplus
#print axioms overlap_card_eq_strict_add_saturated
#print axioms hardProjectionWords_card_eq
#print axioms exponent_capacity_of_hardWords_le_holes
#print axioms exponent_capacity_of_hardWords_le_holes_add_remainingSurplus

end OrderedEdgeColoring
end JSP000404Research
