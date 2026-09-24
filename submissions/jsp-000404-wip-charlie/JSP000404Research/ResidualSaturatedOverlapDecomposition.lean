
import JSP000404Research.ResidualHardRemainder
import JSP000404Research.ResidualMixedOverlapForest
import Mathlib.Tactic

/-!
# Split the hard overlap remainder into mixed and saturated--saturated words

ResidualHardRemainder removes the globally payable strict--strict overlap
words.  Its remaining set saturatedOverlapWords therefore contains every
overlap whose unique residual carrier has at least one saturated endpoint.

This file separates the two genuinely different cases.

A saturated--saturated overlap word is an overlap word for which every
completion-cube carrier vertex has ExactProjectedBudget.  Since every overlap
fibre has exactly two vertices, this means precisely that both endpoints of
its unique residual carrier are saturated.

The complementary hard-overlap set

  mixedHardOverlapWords
    = saturatedOverlapWords \ saturatedSaturatedOverlapWords

is then, under the one-layer residual budget, exactly the mixed case:
one carrier endpoint is saturated and the other is projected-strict.

This gives a clean interface for combining the mixed Kraft-forest results
with a separate treatment of the truly saturated--saturated remainder.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def saturatedSaturatedOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Finset (Fin n → Bool) := by
  classical
  exact (overlapCompletionWords C).filter fun word =>
    ∀ v : V,
      word ∈ retainedCompletionWords C v →
      ExactProjectedBudget C exponent v

@[simp] theorem mem_saturatedSaturatedOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (word : Fin n → Bool) :
    word ∈ saturatedSaturatedOverlapWords C exponent ↔
      word ∈ overlapCompletionWords C ∧
      ∀ v : V,
        word ∈ retainedCompletionWords C v →
        ExactProjectedBudget C exponent v := by
  classical
  simp [saturatedSaturatedOverlapWords]

/-- A saturated--saturated word cannot be strict--strict, hence it lies in the
hard overlap remainder. -/
theorem saturatedSaturatedOverlapWords_subset_saturatedOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    saturatedSaturatedOverlapWords C exponent ⊆
      saturatedOverlapWords C exponent := by
  classical
  intro word hsat
  have hdata :=
    (mem_saturatedSaturatedOverlapWords
      C exponent word).1 hsat
  unfold saturatedOverlapWords
  rw [Finset.mem_sdiff]
  refine ⟨hdata.1, ?_⟩
  intro hstrictStrict
  have hparts := Finset.mem_inter.mp hstrictStrict
  obtain ⟨v, hvSlice, hvWord⟩ :=
    (mem_strictResidualSliceWords
      C exponent false word).1 hparts.1
  have hvStrict :=
    ((mem_strictResidualActiveSlice
      C exponent false v).1 hvSlice).2
  have hvExact := hdata.2 v hvWord
  rw [hvExact] at hvStrict
  exact (lt_irrefl _ hvStrict)

/-- The mixed part of the hard overlap remainder. -/
noncomputable def mixedHardOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Finset (Fin n → Bool) :=
  saturatedOverlapWords C exponent \
    saturatedSaturatedOverlapWords C exponent

@[simp] theorem mem_mixedHardOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (word : Fin n → Bool) :
    word ∈ mixedHardOverlapWords C exponent ↔
      word ∈ saturatedOverlapWords C exponent ∧
      word ∉ saturatedSaturatedOverlapWords C exponent := by
  classical
  simp [mixedHardOverlapWords]

/-- Exact cardinal decomposition of the old hard-overlap remainder. -/
theorem mixedHard_card_add_saturatedSaturated_card_eq_saturatedOverlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (mixedHardOverlapWords C exponent).card +
        (saturatedSaturatedOverlapWords C exponent).card
      =
    (saturatedOverlapWords C exponent).card := by
  classical
  unfold mixedHardOverlapWords
  exact Finset.card_sdiff_add_card_eq_card
    (saturatedSaturatedOverlapWords_subset_saturatedOverlapWords
      C exponent)

/-- The endpoints of every overlap carrier are residual-active. -/
theorem overlap_carrier_endpoints_residual_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {word : Fin n → Bool}
    (hoverlap : word ∈ overlapCompletionWords C) :
    ∃ u v : V,
      u < v ∧
      IsResidual C u v ∧
      word ∈ retainedCompletionWords C u ∧
      word ∈ retainedCompletionWords C v ∧
      residualCoord n ∈ active C u ∧
      residualCoord n ∈ active C v ∧
      ∀ x : V,
        word ∈ retainedCompletionWords C x →
        x = u ∨ x = v := by
  obtain ⟨u, v, huv, hres, huWord, hvWord, huniq⟩ :=
    exists_ordered_residual_pair_of_overlapWord C hoverlap
  have hactive :=
    residualCoord_mem_active_of_isResidual C huv hres
  exact ⟨u, v, huv, hres, huWord, hvWord,
    hactive.1, hactive.2, huniq⟩

/-- Under the one-layer profile hypotheses, a hard mixed word has exactly one
saturated endpoint and one strict endpoint on its unique residual carrier. -/
theorem mixedHardOverlapWord_has_exact_strict_carrier
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {word : Fin n → Bool}
    (hmixed : word ∈ mixedHardOverlapWords C exponent) :
    ∃ u v : V,
      u < v ∧
      IsResidual C u v ∧
      word ∈ retainedCompletionWords C u ∧
      word ∈ retainedCompletionWords C v ∧
      (
        (ExactProjectedBudget C exponent u ∧
          exponent v < projectedFree C v)
        ∨
        (exponent u < projectedFree C u ∧
          ExactProjectedBudget C exponent v)
      ) := by
  have hmixedData :=
    (mem_mixedHardOverlapWords C exponent word).1 hmixed
  have hoverlap :
      word ∈ overlapCompletionWords C := by
    exact (Finset.mem_sdiff.mp hmixedData.1).1
  obtain ⟨u, v, huv, hres, huWord, hvWord,
      huRes, hvRes, huniq⟩ :=
    overlap_carrier_endpoints_residual_active C hoverlap
  have huCase :=
    residual_active_projected_budget_dichotomy
      C exponent hexp honeLoss huRes
  have hvCase :=
    residual_active_projected_budget_dichotomy
      C exponent hexp honeLoss hvRes
  have hnotBothStrict :
      ¬ (exponent u < projectedFree C u ∧
         exponent v < projectedFree C v) := by
    rintro ⟨huStrict, hvStrict⟩
    have huFalse :
        bit C u (residualCoord n) = false := by
      have hcol :
          C.color u v = residualCoord n := by
        apply Fin.ext
        simpa [residualCoord] using residual_val_eq C hres
      have h := edgeColor_bit_lower_eq_false C huv
      simpa [hcol] using h
    have hvTrue :
        bit C v (residualCoord n) = true := by
      have hcol :
          C.color u v = residualCoord n := by
        apply Fin.ext
        simpa [residualCoord] using residual_val_eq C hres
      have h := edgeColor_bit_upper_eq_true C huv
      simpa [hcol] using h
    have huSlice :
        u ∈ strictResidualActiveSlice C exponent false := by
      apply (mem_strictResidualActiveSlice
        C exponent false u).2
      refine ⟨?_, huStrict⟩
      exact (mem_residualActiveSlice C false u).2
        ⟨huRes, huFalse⟩
    have hvSlice :
        v ∈ strictResidualActiveSlice C exponent true := by
      apply (mem_strictResidualActiveSlice
        C exponent true v).2
      refine ⟨?_, hvStrict⟩
      exact (mem_residualActiveSlice C true v).2
        ⟨hvRes, hvTrue⟩
    have hstrictWord :
        word ∈ strictStrictOverlapWords C exponent := by
      apply Finset.mem_inter.mpr
      constructor
      · apply (mem_strictResidualSliceWords
          C exponent false word).2
        exact ⟨u, huSlice, huWord⟩
      · apply (mem_strictResidualSliceWords
          C exponent true word).2
        exact ⟨v, hvSlice, hvWord⟩
    exact (Finset.mem_sdiff.mp hmixedData.1).2 hstrictWord
  have hnotBothExact :
      ¬ (ExactProjectedBudget C exponent u ∧
         ExactProjectedBudget C exponent v) := by
    rintro ⟨huExact, hvExact⟩
    apply hmixedData.2
    apply (mem_saturatedSaturatedOverlapWords
      C exponent word).2
    refine ⟨hoverlap, ?_⟩
    intro x hx
    rcases huniq x hx with rfl | rfl
    · exact huExact
    · exact hvExact
  rcases huCase with huExact | huStrict <;>
    rcases hvCase with hvExact | hvStrict
  · exact False.elim (hnotBothExact ⟨huExact, hvExact⟩)
  · exact ⟨u, v, huv, hres, huWord, hvWord,
      Or.inl ⟨huExact, by omega⟩⟩
  · exact ⟨u, v, huv, hres, huWord, hvWord,
      Or.inr ⟨by omega, hvExact⟩⟩
  · exact False.elim
      (hnotBothStrict ⟨by omega, by omega⟩)

/-- Conversely, an overlap carrier with two exact endpoints contributes only
saturated--saturated words. -/
theorem carrierOverlapWords_subset_saturatedSaturated_of_both_exact
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (huv : u < v)
    (huExact : ExactProjectedBudget C exponent u)
    (hvExact : ExactProjectedBudget C exponent v) :
    carrierOverlapWords C (u,v) ⊆
      saturatedSaturatedOverlapWords C exponent := by
  intro word hword
  have hparts :=
    (mem_carrierOverlapWords C (u,v) word).1 hword
  have hoverlap :=
    mem_overlapCompletionWords_of_common_ordered_pair
      C huv hparts.1 hparts.2
  obtain ⟨a, b, hab, _hres, haWord, hbWord, huniq⟩ :=
    exists_ordered_residual_pair_of_overlapWord C hoverlap
  have hpairs :=
    ordered_residual_pair_unique_of_overlapWord
      C hoverlap huv hab
      hparts.1 hparts.2 haWord hbWord
  have hua : u = a := hpairs.1
  have hvb : v = b := hpairs.2
  apply (mem_saturatedSaturatedOverlapWords
    C exponent word).2
  refine ⟨hoverlap, ?_⟩
  intro x hx
  rcases huniq x hx with hxa | hxb
  · rw [hxa, ← hua]
    exact huExact
  · rw [hxb, ← hvb]
    exact hvExact

#print axioms saturatedSaturatedOverlapWords_subset_saturatedOverlapWords
#print axioms mixedHard_card_add_saturatedSaturated_card_eq_saturatedOverlap
#print axioms mixedHardOverlapWord_has_exact_strict_carrier
#print axioms carrierOverlapWords_subset_saturatedSaturated_of_both_exact

end OrderedEdgeColoring
end JSP000404Research
