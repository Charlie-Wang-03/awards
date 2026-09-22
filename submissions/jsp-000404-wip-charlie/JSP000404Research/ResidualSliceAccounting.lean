
import JSP000404Research.ResidualSliceSeparation
import Mathlib.Tactic

/-!
# Exact set accounting for the two residual-bit slices

ResidualSliceSeparation proves that residual-active completion cubes are
pairwise disjoint inside each canonical residual-bit class.

Let

  A_b = union of Q_v over residual-active vertices with residual bit b.

Then every projected overlap word lies in exactly one cube of A_false and
exactly one cube of A_true. Conversely, any word in both slice unions lies in
two distinct completion cubes and is therefore an overlap word.

Hence

  overlapCompletionWords = A_false ∩ A_true.

This turns the projected-overlap term into an ordinary intersection of two
internally disjoint subcube packings.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

noncomputable def residualSliceCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b : Bool) : Finset (Fin n → Bool) :=
  (residualActiveSlice C b).biUnion
    (retainedCompletionWords C)

@[simp] theorem mem_residualSliceCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b : Bool) (word : Fin n → Bool) :
    word ∈ residualSliceCompletionWords C b ↔
      ∃ v, v ∈ residualActiveSlice C b ∧
        word ∈ retainedCompletionWords C v := by
  classical
  simp [residualSliceCompletionWords]

/-- Internal pairwise disjointness gives exact slice-union cardinality. -/
theorem residualSliceCompletionWords_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (b : Bool) :
    (residualSliceCompletionWords C b).card =
      ∑ v ∈ residualActiveSlice C b,
        (retainedCompletionWords C v).card := by
  classical
  rw [residualSliceCompletionWords,
      Finset.card_biUnion
        (residualActiveSlice_pairwiseDisjoint C b)]

/-- Every overlap word lies in both opposite residual-bit slice unions. -/
theorem overlapCompletionWords_subset_slice_inter
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    overlapCompletionWords C ⊆
      residualSliceCompletionWords C false ∩
        residualSliceCompletionWords C true := by
  classical
  intro word hword
  obtain ⟨u, v, huv, huWord, hvWord, huFalse, hvTrue⟩ :=
    overlapWord_has_opposite_residual_bits C hword
  have hres :
      IsResidual C u v := by
    exact
      (exists_ordered_residual_pair_of_overlapWord C hword).choose_spec.2.1
  have hactive :=
    residualCoord_mem_active_of_isResidual C huv hres
  rw [Finset.mem_inter]
  constructor
  · apply (mem_residualSliceCompletionWords C false word).2
    refine ⟨u, ?_, huWord⟩
    exact (mem_residualActiveSlice C false u).2
      ⟨hactive.1, huFalse⟩
  · apply (mem_residualSliceCompletionWords C true word).2
    refine ⟨v, ?_, hvWord⟩
    exact (mem_residualActiveSlice C true v).2
      ⟨hactive.2, hvTrue⟩

/-- Any word lying in both residual-bit slice unions is genuinely
double-covered. -/
theorem slice_inter_subset_overlapCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    residualSliceCompletionWords C false ∩
        residualSliceCompletionWords C true
      ⊆ overlapCompletionWords C := by
  classical
  intro word hword
  rw [Finset.mem_inter] at hword
  obtain ⟨u, huSlice, huWord⟩ :=
    (mem_residualSliceCompletionWords C false word).1 hword.1
  obtain ⟨v, hvSlice, hvWord⟩ :=
    (mem_residualSliceCompletionWords C true word).1 hword.2
  have huData := (mem_residualActiveSlice C false u).1 huSlice
  have hvData := (mem_residualActiveSlice C true v).1 hvSlice
  have huv : u ≠ v := by
    intro huvEq
    subst v
    rw [huData.2] at hvData
    simp at hvData
  have huF :
      u ∈ completionFibre C word :=
    (mem_completionFibre C word u).2 huWord
  have hvF :
      v ∈ completionFibre C word :=
    (mem_completionFibre C word v).2 hvWord
  have hnontrivial :
      (completionFibre C word).Nontrivial :=
    ⟨u, huF, v, hvF, huv⟩
  have htwoLower :
      2 ≤ (completionFibre C word).card :=
    hnontrivial.two_le_card
  have htwoUpper :=
    completionFibre_card_le_two C word
  apply (mem_overlapCompletionWords C word).2
  omega

/-- Exact identification of the projected overlap set. -/
theorem overlapCompletionWords_eq_slice_inter
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    overlapCompletionWords C =
      residualSliceCompletionWords C false ∩
        residualSliceCompletionWords C true := by
  apply Finset.Subset.antisymm
  · exact overlapCompletionWords_subset_slice_inter C
  · exact slice_inter_subset_overlapCompletionWords C

/-- Cardinal form. -/
theorem overlapCompletionWords_card_eq_slice_inter
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (overlapCompletionWords C).card =
      (residualSliceCompletionWords C false ∩
        residualSliceCompletionWords C true).card := by
  rw [overlapCompletionWords_eq_slice_inter C]

#print axioms residualSliceCompletionWords_card
#print axioms overlapCompletionWords_eq_slice_inter
#print axioms overlapCompletionWords_card_eq_slice_inter

end OrderedEdgeColoring
end JSP000404Research
