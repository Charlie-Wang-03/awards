
import JSP000404Research.ResidualStrictOverlapPayment
import JSP000404Research.ResidualCompletionAccounting
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# The residual master problem reduces to saturated overlaps plus profile loss

Strict--strict projected overlaps are already globally paid by profile surplus.
The only overlap words left after removing them are saturatedOverlapWords.

This file turns that observation into a final accounting outlet.

Let

  H = 2^n - card(coveredCompletionWords)

be the number of Boolean holes.

If

  card(saturatedOverlapWords) + totalProfileLoss <= H,

then the sharp target mass is at most 2^n.

Indeed:

* overlapCompletionWords is the disjoint union of the strict--strict part and
  saturatedOverlapWords;
* the strict--strict part is paid by a subset of total profile surplus;
* the remaining saturated overlap cost and all profile loss are paid by holes.

Thus the remaining geometric/combinatorial problem can be stated without any
threshold-majorization or comb profile:

  inject / charge the concrete hard-word set
    saturatedOverlapWords + lossCompletionWords
  into Boolean holes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

/-- The two strict residual-bit slices are disjoint as vertex sets. -/
theorem strictResidualActiveSlice_false_disjoint_true
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
    (mem_strictResidualActiveSlice C exponent false v).1 hvF
  have hT :=
    (mem_strictResidualActiveSlice C exponent true v).1 hvT
  have hFb := (mem_residualActiveSlice C false v).1 hF.1
  have hTb := (mem_residualActiveSlice C true v).1 hT.1
  rw [hFb.2] at hTb
  simp at hTb

/-- The strict-slice surplus used to pay strict--strict overlaps is bounded by
the total profile surplus. -/
theorem strict_slice_surplus_le_total_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    strictResidualSliceSurplus C exponent false +
        strictResidualSliceSurplus C exponent true
      ≤
    totalDyadicProfileSurplus exponent (projectedFree C) := by
  classical
  let S0 := strictResidualActiveSlice C exponent false
  let S1 := strictResidualActiveSlice C exponent true
  let f : V → ℕ :=
    fun v => dyadicProfileSurplus exponent (projectedFree C) v
  have hdisj : Disjoint S0 S1 := by
    exact strictResidualActiveSlice_false_disjoint_true C exponent
  have hsumUnion :
      (∑ v ∈ S0, f v) + (∑ v ∈ S1, f v) =
        ∑ v ∈ S0 ∪ S1, f v := by
    rw [Finset.sum_union hdisj]
  have hsub :
      S0 ∪ S1 ⊆ (Finset.univ : Finset V) :=
    Finset.subset_univ _
  have hle :
      (∑ v ∈ S0 ∪ S1, f v) ≤
        ∑ v ∈ (Finset.univ : Finset V), f v :=
    Finset.sum_le_sum_of_subset hsub
  unfold strictResidualSliceSurplus totalDyadicProfileSurplus
  change
    (∑ v ∈ S0, f v) + (∑ v ∈ S1, f v) ≤
      ∑ v ∈ (Finset.univ : Finset V), f v
  rw [hsumUnion]
  exact hle

/-- Strict--strict overlap mass is bounded by total profile surplus. -/
theorem strictStrictOverlap_card_le_total_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (strictStrictOverlapWords C exponent).card ≤
      totalDyadicProfileSurplus exponent (projectedFree C) := by
  exact
    (strictStrictOverlap_card_le_slice_surplus C exponent).trans
      (strict_slice_surplus_le_total_surplus C exponent)

/-- Exact overlap-cardinality decomposition into payable strict--strict words
and the saturated remainder. -/
theorem saturatedOverlap_card_add_strict_eq_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (saturatedOverlapWords C exponent).card +
        (strictStrictOverlapWords C exponent).card =
      (overlapCompletionWords C).card := by
  classical
  unfold saturatedOverlapWords
  exact Finset.card_sdiff_add_card_eq_card
    (strictStrictOverlap_subset_overlapCompletionWords
      C exponent)

/-- Main hard-remainder outlet.

Once saturated overlap words plus profile-loss mass fit into the uncovered
Boolean words, all remaining overlap is paid by profile surplus and the sharp
capacity follows. -/
theorem exponent_capacity_of_saturated_overlap_and_loss_fit_holes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hholes :
      (saturatedOverlapWords C exponent).card +
          totalDyadicProfileLoss exponent (projectedFree C)
        ≤
      2 ^ n - (coveredCompletionWords C).card) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  apply exponent_capacity_of_completion_defect_payment
    C exponent
  have hstrict :=
    strictStrictOverlap_card_le_total_surplus
      C exponent
  have hsplit :=
    saturatedOverlap_card_add_strict_eq_overlap
      C exponent
  omega

/-- Equivalent concrete loss-word formulation under the one-layer hypothesis. -/
theorem exponent_capacity_of_hard_words_fit_holes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hholes :
      (saturatedOverlapWords C exponent).card +
          (lossCompletionWords C exponent).card
        ≤
      2 ^ n - (coveredCompletionWords C).card) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  apply exponent_capacity_of_saturated_overlap_and_loss_fit_holes
    C exponent
  rw [← lossCompletionWords_card_eq_totalDyadicProfileLoss
      C exponent hexp honeLoss]
  exact hholes

#print axioms strict_slice_surplus_le_total_surplus
#print axioms strictStrictOverlap_card_le_total_surplus
#print axioms saturatedOverlap_card_add_strict_eq_overlap
#print axioms exponent_capacity_of_saturated_overlap_and_loss_fit_holes
#print axioms exponent_capacity_of_hard_words_fit_holes

end OrderedEdgeColoring
end JSP000404Research
