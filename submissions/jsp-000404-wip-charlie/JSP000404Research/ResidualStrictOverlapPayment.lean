
import JSP000404Research.ResidualOverlapPairDecomposition
import JSP000404Research.ResidualSaturationBridge
import Mathlib.Tactic

/-!
# Global payment of strict--strict projected overlaps

Charging each overlap carrier separately would double-count endpoint surplus
when the residual graph has high degree.  The canonical residual-bit slices
avoid this.

Fix the vertices which are residual-active and have strict projected slack

  exponent(v) < projectedFree(v).

Inside each residual-bit slice their completion cubes are pairwise disjoint.
Moreover strict dyadic slack pays at least half of each projected cube:

  2^projectedFree(v) <=
    2 * dyadicProfileSurplus(exponent,projectedFree)(v).

Let F and T be the unions of strict completion cubes in the false and true
residual-bit slices.  Their intersection O is exactly the set of overlap words
whose two carrier endpoints are both strict.  Since

  card O <= card F,
  card O <= card T,

we have

  2 card O <= card F + card T

and the two strict-slice surplus sums pay O globally.

Thus no endpoint surplus is charged once per incident residual edge.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

noncomputable def strictResidualActiveSlice
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (b : Bool) : Finset V := by
  classical
  exact (residualActiveSlice C b).filter fun v =>
    exponent v < projectedFree C v

@[simp] theorem mem_strictResidualActiveSlice
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (b : Bool) (v : V) :
    v ∈ strictResidualActiveSlice C exponent b ↔
      v ∈ residualActiveSlice C b ∧
      exponent v < projectedFree C v := by
  classical
  simp [strictResidualActiveSlice]

noncomputable def strictResidualSliceWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (b : Bool) : Finset (Fin n → Bool) :=
  (strictResidualActiveSlice C exponent b).biUnion
    (retainedCompletionWords C)

@[simp] theorem mem_strictResidualSliceWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (b : Bool) (word : Fin n → Bool) :
    word ∈ strictResidualSliceWords C exponent b ↔
      ∃ v, v ∈ strictResidualActiveSlice C exponent b ∧
        word ∈ retainedCompletionWords C v := by
  classical
  simp [strictResidualSliceWords]

theorem strictResidualSlice_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (b : Bool) :
    ((strictResidualActiveSlice C exponent b : Finset V) : Set V).PairwiseDisjoint
      (retainedCompletionWords C) := by
  intro u hu v hv huv
  have hu' :
      u ∈ residualActiveSlice C b :=
    ((mem_strictResidualActiveSlice C exponent b u).1 hu).1
  have hv' :
      v ∈ residualActiveSlice C b :=
    ((mem_strictResidualActiveSlice C exponent b v).1 hv).1
  exact residualActiveSlice_pairwiseDisjoint C b hu' hv' huv

theorem strictResidualSliceWords_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (b : Bool) :
    (strictResidualSliceWords C exponent b).card =
      ∑ v ∈ strictResidualActiveSlice C exponent b,
        (retainedCompletionWords C v).card := by
  classical
  rw [strictResidualSliceWords,
      Finset.card_biUnion
        (strictResidualSlice_pairwiseDisjoint
          C exponent b)]

noncomputable def strictResidualSliceSurplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (b : Bool) : ℕ :=
  ∑ v ∈ strictResidualActiveSlice C exponent b,
    dyadicProfileSurplus exponent (projectedFree C) v

/-- One strict endpoint's projected cube is at most twice its profile surplus. -/
theorem retainedCompletionWords_card_le_two_mul_surplus_of_strict
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hstrict : exponent v < projectedFree C v) :
    (retainedCompletionWords C v).card ≤
      2 * dyadicProfileSurplus exponent (projectedFree C) v := by
  rw [retainedCompletionWords_card]
  unfold dyadicProfileSurplus
  have hhalf :=
    half_pow_le_dyadic_surplus_of_lt hstrict
  have hnuPos : 1 ≤ projectedFree C v := by omega
  have hpow :
      2 ^ projectedFree C v =
        2 * 2 ^ (projectedFree C v - 1) := by
    have hsucc :
        projectedFree C v - 1 + 1 = projectedFree C v := by
      omega
    calc
      2 ^ projectedFree C v
          = 2 ^ (projectedFree C v - 1 + 1) := by rw [hsucc]
      _ = 2 ^ (projectedFree C v - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (projectedFree C v - 1) := by omega
  omega

/-- The total strict-slice projected mass is at most twice that slice's total
profile surplus. -/
theorem strictResidualSliceWords_card_le_two_mul_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (b : Bool) :
    (strictResidualSliceWords C exponent b).card ≤
      2 * strictResidualSliceSurplus C exponent b := by
  rw [strictResidualSliceWords_card]
  unfold strictResidualSliceSurplus
  have hsum :
      (∑ v ∈ strictResidualActiveSlice C exponent b,
          (retainedCompletionWords C v).card)
        ≤
      ∑ v ∈ strictResidualActiveSlice C exponent b,
          2 * dyadicProfileSurplus exponent (projectedFree C) v := by
    apply Finset.sum_le_sum
    intro v hv
    exact retainedCompletionWords_card_le_two_mul_surplus_of_strict
      C exponent
      ((mem_strictResidualActiveSlice C exponent b v).1 hv).2
  rw [← Finset.mul_sum] at hsum
  exact hsum

noncomputable def strictStrictOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Finset (Fin n → Bool) :=
  strictResidualSliceWords C exponent false ∩
    strictResidualSliceWords C exponent true

/-- Global strict--strict overlap payment without edgewise double counting. -/
theorem strictStrictOverlap_card_le_slice_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (strictStrictOverlapWords C exponent).card ≤
      strictResidualSliceSurplus C exponent false +
        strictResidualSliceSurplus C exponent true := by
  classical
  have hfalse :
      (strictStrictOverlapWords C exponent).card ≤
        (strictResidualSliceWords C exponent false).card :=
    Finset.card_le_card Finset.inter_subset_left
  have htrue :
      (strictStrictOverlapWords C exponent).card ≤
        (strictResidualSliceWords C exponent true).card :=
    Finset.card_le_card Finset.inter_subset_right
  have hmassFalse :=
    strictResidualSliceWords_card_le_two_mul_surplus
      C exponent false
  have hmassTrue :=
    strictResidualSliceWords_card_le_two_mul_surplus
      C exponent true
  omega

/-- Every strict--strict slice-intersection word is a genuine global overlap
word. -/
theorem strictStrictOverlap_subset_overlapCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    strictStrictOverlapWords C exponent ⊆
      overlapCompletionWords C := by
  intro word hword
  have hparts := Finset.mem_inter.mp hword
  obtain ⟨u, huSlice, huWord⟩ :=
    (mem_strictResidualSliceWords
      C exponent false word).1 hparts.1
  obtain ⟨v, hvSlice, hvWord⟩ :=
    (mem_strictResidualSliceWords
      C exponent true word).1 hparts.2
  have huBase :=
    ((mem_strictResidualActiveSlice
      C exponent false u).1 huSlice).1
  have hvBase :=
    ((mem_strictResidualActiveSlice
      C exponent true v).1 hvSlice).1
  have huv : u ≠ v := by
    intro huvEq
    subst v
    have huData := (mem_residualActiveSlice C false u).1 huBase
    have hvData := (mem_residualActiveSlice C true u).1 hvBase
    have huBit := huData.2
    have hvBit := hvData.2
    rw [huBit] at hvBit
    simp at hvBit
  rcases lt_or_gt_of_ne huv with huvlt | hvult
  · exact mem_overlapCompletionWords_of_common_ordered_pair
      C huvlt huWord hvWord
  · exact mem_overlapCompletionWords_of_common_ordered_pair
      C hvult hvWord huWord

/-- The remaining hard overlap words after removing globally payable
strict--strict intersections. -/
noncomputable def saturatedOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Finset (Fin n → Bool) :=
  overlapCompletionWords C  strictStrictOverlapWords C exponent

/-- Under the one-layer residual budget, every remaining overlap word has a
carrier with at least one saturated endpoint. -/
theorem saturatedOverlapWord_has_saturated_carrier
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {word : Fin n → Bool}
    (hword : word ∈ saturatedOverlapWords C exponent) :
    ∃ u v : V,
      u < v ∧
      IsResidual C u v ∧
      word ∈ retainedCompletionWords C u ∧
      word ∈ retainedCompletionWords C v ∧
      (exponent u = projectedFree C u ∨
       exponent v = projectedFree C v) := by
  have hoverlap :
      word ∈ overlapCompletionWords C :=
    (Finset.mem_sdiff.mp hword).1
  obtain ⟨u, v, huv, hres, huWord, hvWord, _⟩ :=
    exists_ordered_residual_pair_of_overlapWord C hoverlap
  refine ⟨u, v, huv, hres, huWord, hvWord, ?_⟩
  by_contra hsat
  push_neg at hsat
  have huRes :=
    (residualCoord_mem_active_of_isResidual C huv hres).1
  have hvRes :=
    (residualCoord_mem_active_of_isResidual C huv hres).2
  have huLe :=
    exponent_le_projectedFree_of_residual_mem
      C exponent hexp honeLoss huRes
  have hvLe :=
    exponent_le_projectedFree_of_residual_mem
      C exponent hexp honeLoss hvRes
  have huStrict : exponent u < projectedFree C u := by omega
  have hvStrict : exponent v < projectedFree C v := by omega
  have huFalse := edgeColor_bit_lower_eq_false C huv
  have hvTrue := edgeColor_bit_upper_eq_true C huv
  have hcol :
      C.color u v = residualCoord n := by
    apply Fin.ext
    simpa [residualCoord] using residual_val_eq C hres
  rw [hcol] at huFalse hvTrue
  have huSlice :
      u ∈ strictResidualActiveSlice C exponent false := by
    apply (mem_strictResidualActiveSlice C exponent false u).2
    exact ⟨
      (mem_residualActiveSlice C false u).2
        ⟨huRes, huFalse⟩,
      huStrict⟩
  have hvSlice :
      v ∈ strictResidualActiveSlice C exponent true := by
    apply (mem_strictResidualActiveSlice C exponent true v).2
    exact ⟨
      (mem_residualActiveSlice C true v).2
        ⟨hvRes, hvTrue⟩,
      hvStrict⟩
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
  exact (Finset.mem_sdiff.mp hword).2 hstrictWord

#print axioms strictResidualSliceWords_card_le_two_mul_surplus
#print axioms strictStrictOverlap_card_le_slice_surplus
#print axioms saturatedOverlapWord_has_saturated_carrier

end OrderedEdgeColoring
end JSP000404Research
