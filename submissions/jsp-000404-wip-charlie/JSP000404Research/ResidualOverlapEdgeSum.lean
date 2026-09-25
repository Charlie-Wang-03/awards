
import JSP000404Research.ResidualOverlapDimension
import JSP000404Research.ResidualOverlapWitness
import Mathlib.Tactic

/-!
# Projected overlap mass as an exact residual-edge sum

Every overlap word determines a unique ordered residual pair u<v.
Conversely, every word in Q_u inter Q_v for distinct u<v is an overlap word.

Hence the nonempty pair intersections form a pairwise-disjoint partition of
overlapCompletionWords.

ResidualOverlapDimension computes each block exactly as

  card(Q_u inter Q_v) = 2 ^ card(commonInactiveRetained(u,v)).

Therefore

  overlapMass =
    sum over overlap-carrying ordered residual pairs of 2^h_uv.

This is the edgewise form needed for weighted charging.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

noncomputable def overlapResidualPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (V × V) := by
  classical
  exact Finset.univ.filter fun e =>
    e.1 < e.2 ∧
    (retainedCompletionWords C e.1 ∩
      retainedCompletionWords C e.2).Nonempty

@[simp] theorem mem_overlapResidualPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (u,v) ∈ overlapResidualPairs C ↔
      u < v ∧
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).Nonempty := by
  classical
  simp [overlapResidualPairs]

noncomputable def pairOverlapWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (e : V × V) : Finset (Fin n → Bool) :=
  retainedCompletionWords C e.1 ∩
    retainedCompletionWords C e.2

/-- Every listed pair is genuinely residual. -/
theorem isResidual_of_mem_overlapResidualPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hpair : (u,v) ∈ overlapResidualPairs C) :
    IsResidual C u v := by
  have hp :=
    (mem_overlapResidualPairs C u v).1 hpair
  obtain ⟨word, hword⟩ := hp.2
  have hmem := Finset.mem_inter.mp hword
  exact isResidual_of_retainedCompletion_overlap_lt
    C hp.1 hmem.1 hmem.2

/-- Different ordered overlap pairs have disjoint intersection-word blocks. -/
theorem pairOverlapWords_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    ((overlapResidualPairs C : Finset (V × V)) : Set (V × V)).PairwiseDisjoint
      (pairOverlapWords C) := by
  intro e he f hf hef
  classical
  rw [Finset.disjoint_left]
  intro word hwe hwf
  have heData :=
    (mem_overlapResidualPairs C e.1 e.2).1 he
  have hfData :=
    (mem_overlapResidualPairs C f.1 f.2).1 hf
  have hwe' := Finset.mem_inter.mp hwe
  have hwf' := Finset.mem_inter.mp hwf
  have hoverlap :
      word ∈ overlapCompletionWords C := by
    have huF :
        e.1 ∈ completionFibre C word :=
      (mem_completionFibre C word e.1).2 hwe'.1
    have hvF :
        e.2 ∈ completionFibre C word :=
      (mem_completionFibre C word e.2).2 hwe'.2
    have hnontrivial :
        (completionFibre C word).Nontrivial :=
      ⟨e.1, huF, e.2, hvF, ne_of_lt heData.1⟩
    have hlo := hnontrivial.two_le_card
    have hhi := completionFibre_card_le_two C word
    apply (mem_overlapCompletionWords C word).2
    omega
  have huniq :=
    ordered_residual_pair_unique_of_overlapWord
      C hoverlap
      heData.1 hfData.1
      hwe'.1 hwe'.2 hwf'.1 hwf'.2
  apply hef
  exact Prod.ext huniq.1 huniq.2

/-- The overlap-word set is exactly the disjoint union of pair intersections. -/
theorem overlapCompletionWords_eq_pair_biUnion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    overlapCompletionWords C =
      (overlapResidualPairs C).biUnion
        (pairOverlapWords C) := by
  classical
  apply Finset.ext
  intro word
  constructor
  · intro hoverlap
    obtain ⟨u, v, huv, _hres, hu, hv, _huniq⟩ :=
      exists_ordered_residual_pair_of_overlapWord C hoverlap
    have hpair :
        (u,v) ∈ overlapResidualPairs C := by
      apply (mem_overlapResidualPairs C u v).2
      exact ⟨huv, ⟨word, Finset.mem_inter.mpr ⟨hu,hv⟩⟩⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(u,v), hpair, ?_⟩
    exact Finset.mem_inter.mpr ⟨hu,hv⟩
  · intro hword
    obtain ⟨e, he, hwe⟩ :=
      Finset.mem_biUnion.mp hword
    have heData :=
      (mem_overlapResidualPairs C e.1 e.2).1 he
    have hwe' := Finset.mem_inter.mp hwe
    have huF :
        e.1 ∈ completionFibre C word :=
      (mem_completionFibre C word e.1).2 hwe'.1
    have hvF :
        e.2 ∈ completionFibre C word :=
      (mem_completionFibre C word e.2).2 hwe'.2
    have hnontrivial :
        (completionFibre C word).Nontrivial :=
      ⟨e.1, huF, e.2, hvF, ne_of_lt heData.1⟩
    have hlo := hnontrivial.two_le_card
    have hhi := completionFibre_card_le_two C word
    apply (mem_overlapCompletionWords C word).2
    omega

/-- Exact block-sum formula before inserting the power-of-two dimension. -/
theorem overlapCompletionWords_card_eq_pair_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (overlapCompletionWords C).card =
      ∑ e ∈ overlapResidualPairs C,
        (pairOverlapWords C e).card := by
  classical
  rw [overlapCompletionWords_eq_pair_biUnion C,
      Finset.card_biUnion
        (pairOverlapWords_pairwiseDisjoint C)]

/-- Final edgewise overlap-mass identity. -/
theorem overlapCompletionWords_card_eq_edgeWeight_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (overlapCompletionWords C).card =
      ∑ e ∈ overlapResidualPairs C,
        2 ^ (commonInactiveRetained C e.1 e.2).card := by
  classical
  rw [overlapCompletionWords_card_eq_pair_sum C]
  apply Finset.sum_congr rfl
  intro e he
  have heData :=
    (mem_overlapResidualPairs C e.1 e.2).1 he
  obtain ⟨base, hbase⟩ := heData.2
  have hb := Finset.mem_inter.mp hbase
  exact retainedCompletionWords_inter_card_eq_pow_commonInactive
    C hb.1 hb.2

#print axioms pairOverlapWords_pairwiseDisjoint
#print axioms overlapCompletionWords_eq_pair_biUnion
#print axioms overlapCompletionWords_card_eq_edgeWeight_sum

end OrderedEdgeColoring
end JSP000404Research
