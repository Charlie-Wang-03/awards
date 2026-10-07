import JSP000404Research.NearPerfectMinimalRank
import JSP000404Research.ResidualSaturatedOverlapDecomposition
import Mathlib.Tactic

/-!
# Exact classification of one hard projection word

A hard word is, by definition, either

* a projected-loss completion word, or
* a saturated overlap word.

The saturated-overlap branch then splits disjointly into

* mixed hard overlap;
* saturated--saturated overlap.

This file packages that three-way classification directly on the subtype
HardProjectionWord.  It is the entry point for the minimal-rank augmenting
argument: choose one rank-minimal hard word and analyze only these three local
types.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem hardProjectionWord_loss_or_mixed_or_saturatedSaturated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (x : HardProjectionWord C exponent) :
    x.1 ∈ lossCompletionWords C exponent
    ∨ x.1 ∈ mixedHardOverlapWords C exponent
    ∨ x.1 ∈ saturatedSaturatedOverlapWords C exponent := by
  classical
  have hx := x.2
  unfold hardProjectionWords at hx
  rw [Finset.mem_union] at hx
  rcases hx with hsat | hloss
  · by_cases hss :
      x.1 ∈ saturatedSaturatedOverlapWords C exponent
    · exact Or.inr (Or.inr hss)
    · right
      left
      apply (mem_mixedHardOverlapWords C exponent x.1).2
      exact ⟨hsat,hss⟩
  · exact Or.inl hloss

theorem hardProjectionWord_not_loss_of_mixed
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {x : Fin n → Bool}
    (hmixed : x ∈ mixedHardOverlapWords C exponent) :
    x ∉ lossCompletionWords C exponent := by
  have hover :
      x ∈ overlapCompletionWords C := by
    have hs :=
      ((mem_mixedHardOverlapWords C exponent x).1 hmixed).1
    exact (Finset.mem_sdiff.mp hs).1
  exact
    Finset.disjoint_left.mp
      (lossCompletionWords_disjoint_overlapCompletionWords
        C exponent hexp honeLoss)
      · intro hloss
        exact hloss
      · exact hover

theorem hardProjectionWord_not_loss_of_saturatedSaturated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {x : Fin n → Bool}
    (hss : x ∈ saturatedSaturatedOverlapWords C exponent) :
    x ∉ lossCompletionWords C exponent := by
  have hover :
      x ∈ overlapCompletionWords C :=
    ((mem_saturatedSaturatedOverlapWords
      C exponent x).1 hss).1
  exact
    Finset.disjoint_left.mp
      (lossCompletionWords_disjoint_overlapCompletionWords
        C exponent hexp honeLoss)
      · intro hloss
        exact hloss
      · exact hover

#print axioms hardProjectionWord_loss_or_mixed_or_saturatedSaturated
#print axioms hardProjectionWord_not_loss_of_mixed
#print axioms hardProjectionWord_not_loss_of_saturatedSaturated

end OrderedEdgeColoring
end JSP000404Research
