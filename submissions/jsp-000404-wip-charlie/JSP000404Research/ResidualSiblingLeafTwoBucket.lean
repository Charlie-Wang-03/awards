import JSP000404Research.ResidualSiblingLeafAggregation
import Mathlib.Tactic

/-!
# Two-bucket sibling charge decomposition at a projected-loss parent

At a projected-loss parent p,

  enlargedBlock(p) = completionCube(p) ∪ allActiveTranslatedWords(p),

and the two regions are disjoint.

For any family of sibling leaves with unique parent p, use each leaf's shared
words as its charge and split those charges into base and translated parts.

The base parts are pairwise disjoint subsets of the single completion cube, so
their total mass is at most one cube.

The translated parts are pairwise disjoint subsets of the translated region.
After subtracting the parent's local slack, their residual mass is at most one
additional cube.

Thus the two-cube overload invariant has a canonical two-bucket realization,
not merely a numerical bound.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def siblingLeafBaseCharge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (parent v : V) : Finset (Fin n → Bool) :=
  siblingLeafCharge C exponent T v ∩
    retainedCompletionWords C parent

noncomputable def siblingLeafTranslatedCharge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (parent v : V) : Finset (Fin n → Bool) :=
  siblingLeafCharge C exponent T v ∩
    allActiveTranslatedWords C parent

theorem siblingLeafCharge_eq_base_union_translated_of_loss_parent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T leaves : Finset V}
    {parent v : V}
    (hparentLoss :
      parent ∈ projectedLossVertices C exponent)
    (hvLeaves : v ∈ leaves)
    (hleavesT : leaves ⊆ T)
    (hparentT : parent ∈ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ u ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ u →
          EnlargedBlocksCross C exponent u z →
          z = parent) :
    siblingLeafCharge C exponent T v =
      siblingLeafBaseCharge C exponent T parent v ∪
      siblingLeafTranslatedCharge C exponent T parent v := by
  have hsub :=
    siblingLeafCharge_subset_parent
      C exponent hvLeaves hleavesT hparentT
      hparentNotLeaf hunique
  ext word
  constructor
  · intro hw
    have hp := hsub hw
    rw [enlargedProjectedCandidateBlock_loss
          C exponent hparentLoss] at hp
    rcases Finset.mem_union.mp hp with hbase | htrans
    · apply Finset.mem_union_left
      exact Finset.mem_inter.mpr ⟨hw,hbase⟩
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hw,htrans⟩
  · intro hw
    rcases Finset.mem_union.mp hw with hbase | htrans
    · exact (Finset.mem_inter.mp hbase).1
    · exact (Finset.mem_inter.mp htrans).1

theorem siblingLeaf_base_translated_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (parent v : V) :
    Disjoint
      (siblingLeafBaseCharge C exponent T parent v)
      (siblingLeafTranslatedCharge C exponent T parent v) := by
  rw [Finset.disjoint_left]
  intro word hb ht
  have hb' := (Finset.mem_inter.mp hb).2
  have ht' := (Finset.mem_inter.mp ht).2
  exact Finset.disjoint_left.mp
    (retainedCompletionWords_disjoint_allActiveTranslatedWords
      C parent)
    hb' ht'

theorem siblingLeaf_base_charge_sum_le_cube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T leaves : Finset V}
    {parent : V}
    (hleavesT : leaves ⊆ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ v ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ v →
          EnlargedBlocksCross C exponent v z →
          z = parent) :
    (∑ v ∈ leaves,
      (siblingLeafBaseCharge C exponent T parent v).card)
      ≤
    (retainedCompletionWords C parent).card := by
  let charge : V → Finset (Fin n → Bool) :=
    fun v => siblingLeafBaseCharge C exponent T parent v
  have hchild :
      ∀ v ∈ leaves,
        charge v ⊆ enlargedProjectedCandidateBlock C exponent v := by
    intro v _hv
    intro word hw
    exact siblingLeafCharge_subset_child C exponent T v
      (Finset.mem_inter.mp hw).1
  have hpairwise :=
    uniqueNeighbourLeafCharges_pairwiseDisjoint
      C exponent charge
      hleavesT hparentNotLeaf hunique hchild
  have hcard :
      (leaves.biUnion charge).card =
        ∑ v ∈ leaves, (charge v).card := by
    rw [Finset.card_biUnion hpairwise]
  have hsub :
      leaves.biUnion charge ⊆ retainedCompletionWords C parent := by
    intro word hw
    obtain ⟨v,hv,hword⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_inter.mp hword).2
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  exact hle

theorem siblingLeaf_translated_charge_sum_le_active_mul_cube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T leaves : Finset V}
    {parent : V}
    (hleavesT : leaves ⊆ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ v ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ v →
          EnlargedBlocksCross C exponent v z →
          z = parent) :
    (∑ v ∈ leaves,
      (siblingLeafTranslatedCharge C exponent T parent v).card)
      ≤
    (retainedActive C parent).card *
      (retainedCompletionWords C parent).card := by
  let charge : V → Finset (Fin n → Bool) :=
    fun v => siblingLeafTranslatedCharge C exponent T parent v
  apply uniqueNeighbourLeafCharges_sum_le_parent_active_mul_cube
    C exponent charge
    hleavesT hparentNotLeaf hunique
  · intro v _hv
    intro word hw
    exact siblingLeafCharge_subset_child C exponent T v
      (Finset.mem_inter.mp hw).1
  · intro v _hv
    exact Finset.inter_subset_right

theorem siblingLeaf_charge_total_eq_base_add_translated_of_loss_parent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T leaves : Finset V}
    {parent : V}
    (hparentLoss :
      parent ∈ projectedLossVertices C exponent)
    (hleavesT : leaves ⊆ T)
    (hparentT : parent ∈ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ v ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ v →
          EnlargedBlocksCross C exponent v z →
          z = parent) :
    (∑ v ∈ leaves,
      (siblingLeafCharge C exponent T v).card)
      =
    (∑ v ∈ leaves,
      (siblingLeafBaseCharge C exponent T parent v).card)
      +
    (∑ v ∈ leaves,
      (siblingLeafTranslatedCharge C exponent T parent v).card) := by
  have hpoint :
      ∀ v ∈ leaves,
        (siblingLeafCharge C exponent T v).card =
          (siblingLeafBaseCharge C exponent T parent v).card +
          (siblingLeafTranslatedCharge C exponent T parent v).card := by
    intro v hv
    rw [siblingLeafCharge_eq_base_union_translated_of_loss_parent
          C exponent hparentLoss hv hleavesT hparentT
          hparentNotLeaf hunique]
    rw [Finset.card_union_of_disjoint
          (siblingLeaf_base_translated_disjoint
            C exponent T parent v)]
  calc
    (∑ v ∈ leaves,
      (siblingLeafCharge C exponent T v).card)
      =
    ∑ v ∈ leaves,
      ((siblingLeafBaseCharge C exponent T parent v).card +
       (siblingLeafTranslatedCharge C exponent T parent v).card) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hpoint v hv
    _ =
      (∑ v ∈ leaves,
        (siblingLeafBaseCharge C exponent T parent v).card)
      +
      (∑ v ∈ leaves,
        (siblingLeafTranslatedCharge C exponent T parent v).card) := by
        rw [Finset.sum_add_distrib]

#print axioms siblingLeafCharge_eq_base_union_translated_of_loss_parent
#print axioms siblingLeaf_base_charge_sum_le_cube
#print axioms siblingLeaf_translated_charge_sum_le_active_mul_cube
#print axioms siblingLeaf_charge_total_eq_base_add_translated_of_loss_parent

end OrderedEdgeColoring
end JSP000404Research
