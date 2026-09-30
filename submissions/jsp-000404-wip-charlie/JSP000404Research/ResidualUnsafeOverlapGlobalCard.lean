import JSP000404Research.ResidualUnsafeCarrierMatchingCard
import JSP000404Research.ResidualOverlapEdgeSum
import Mathlib.Tactic

/-!
# Global cardinality of unsafe projected-overlap words

Unsafe overlap carrier pairs already form a matching.  Separately, every
unsafe overlapping pair has exactly one common retained completion word.

This file combines those facts globally.  Define the unsafe overlap-word set
as the disjoint union of pair-intersection blocks over unsafe carrier pairs.
Because overlap words determine a unique ordered residual carrier, those blocks
are pairwise disjoint.  Every block has cardinality one, hence

  card(unsafeOverlapWords) = card(unsafeOverlapCarrierPairs),

and therefore

  2 * card(unsafeOverlapWords) <= card V.

This removes all Boolean-cube multiplicity from the unsafe part of the hard
residual remainder: globally it costs at most one word per edge of a matching.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def unsafeOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (Fin n → Bool) :=
  (unsafeOverlapCarrierPairs C).biUnion (pairOverlapWords C)

theorem unsafeOverlapCarrierPairs_subset_overlapResidualPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    unsafeOverlapCarrierPairs C ⊆ overlapResidualPairs C := by
  intro e he
  have hdata :=
    (mem_unsafeOverlapCarrierPairs C e.1 e.2).1 he
  apply (mem_overlapResidualPairs C e.1 e.2).2
  refine ⟨hdata.1, ?_⟩
  obtain ⟨word, hu, hv⟩ := hdata.2.2
  exact ⟨word, Finset.mem_inter.mpr ⟨hu, hv⟩⟩

theorem unsafe_pairOverlapWords_card_eq_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {e : V × V}
    (he : e ∈ unsafeOverlapCarrierPairs C) :
    (pairOverlapWords C e).card = 1 := by
  have hdata :=
    (mem_unsafeOverlapCarrierPairs C e.1 e.2).1 he
  obtain ⟨word, hu, hv⟩ := hdata.2.2
  unfold pairOverlapWords
  exact
    retainedCompletionWords_inter_card_one_of_unsafe_overlap
      C hdata.2.1 hu hv

theorem unsafe_pairOverlapWords_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    ((unsafeOverlapCarrierPairs C : Finset (V × V)) : Set (V × V)).
      PairwiseDisjoint (pairOverlapWords C) := by
  intro e he f hf hef
  apply pairOverlapWords_pairwiseDisjoint C
  · exact unsafeOverlapCarrierPairs_subset_overlapResidualPairs C
      (by simpa using he)
  · exact unsafeOverlapCarrierPairs_subset_overlapResidualPairs C
      (by simpa using hf)
  · exact hef

theorem unsafeOverlapWords_card_eq_carrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (unsafeOverlapWords C).card =
      (unsafeOverlapCarrierPairs C).card := by
  classical
  unfold unsafeOverlapWords
  rw [Finset.card_biUnion
    (unsafe_pairOverlapWords_pairwiseDisjoint C)]
  calc
    (∑ e ∈ unsafeOverlapCarrierPairs C,
        (pairOverlapWords C e).card)
        =
      ∑ _e ∈ unsafeOverlapCarrierPairs C, 1 := by
        apply Finset.sum_congr rfl
        intro e he
        exact unsafe_pairOverlapWords_card_eq_one C he
    _ = (unsafeOverlapCarrierPairs C).card := by
        simp

theorem unsafeOverlapWords_two_mul_card_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    2 * (unsafeOverlapWords C).card ≤ Fintype.card V := by
  rw [unsafeOverlapWords_card_eq_carrierPairs C]
  exact unsafeOverlapCarrierPairs_two_mul_card_le C

#print axioms unsafeOverlapCarrierPairs_subset_overlapResidualPairs
#print axioms unsafe_pairOverlapWords_card_eq_one
#print axioms unsafeOverlapWords_card_eq_carrierPairs
#print axioms unsafeOverlapWords_two_mul_card_le

end OrderedEdgeColoring
end JSP000404Research
