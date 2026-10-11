import JSP000404Research.ResidualHardOverlapRigidFaces
import JSP000404Research.ResidualOverlapSurplus
import Mathlib.Tactic

/-!
# Exact dyadic mass of rigid hard overlaps

The hard residual overlap edges decompose into:
1. transportable pairs with an outward/inactive retained coordinate;
2. rigid pairs, where no such coordinate exists.

Rigid pairs have Q_upper ⊆ Q_lower, so their ENTIRE upper
projected cube is overlapped. The overlap words for different
rigid carriers are disjoint by uniqueness of the residual pair.
Their exact total mass is the sum of dyadic upper cube masses.

A further non-circular sufficient condition pays a SINGLE rigid
face with the lower endpoint's dyadic profile surplus alone:
projectedFree(upper) < projectedFree(lower) AND
exponent(lower) < projectedFree(lower).

The remaining rigid face types (projected-free equality, or
saturated lower endpoints) are explicitly not charged.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def rigidHardOverlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (V × V) := by
  classical
  exact (hardOverlapCarrierPairs C).filter
    (fun p => ¬ HasOutgoingHardTransport C p.1 p.2)

@[simp] theorem mem_rigidHardOverlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (p : V × V) :
    p ∈ rigidHardOverlapCarrierPairs C ↔
    p ∈ hardOverlapCarrierPairs C ∧
      ¬ HasOutgoingHardTransport C p.1 p.2 := by
  classical
  simp [rigidHardOverlapCarrierPairs]

noncomputable def transportableHardOverlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (V × V) := by
  classical
  exact (hardOverlapCarrierPairs C).filter
    (fun p => HasOutgoingHardTransport C p.1 p.2)

@[simp] theorem mem_transportableHardOverlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (p : V × V) :
    p ∈ transportableHardOverlapCarrierPairs C ↔
    p ∈ hardOverlapCarrierPairs C ∧
      HasOutgoingHardTransport C p.1 p.2 := by
  classical
  simp [transportableHardOverlapCarrierPairs]

noncomputable def rigidHardOverlapCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (Fin n → Bool) :=
  (rigidHardOverlapCarrierPairs C).biUnion (carrierOverlapWords C)

noncomputable def transportableHardOverlapCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (Fin n → Bool) :=
  (transportableHardOverlapCarrierPairs C).biUnion (carrierOverlapWords C)

/-- Rigid and transportable hard carrier sets partition ALL
same-retained overlapping residual carriers. -/
theorem hard_overlap_carriers_eq_transportable_union_rigid
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    hardOverlapCarrierPairs C =
      transportableHardOverlapCarrierPairs C ∪
        rigidHardOverlapCarrierPairs C := by
  classical
  ext p
  simp only [mem_hardOverlapCarrierPairs,
    Finset.mem_union, mem_transportableHardOverlapCarrierPairs,
    mem_rigidHardOverlapCarrierPairs]
  constructor
  · intro hp
    by_cases h : HasOutgoingHardTransport C p.1 p.2
    · exact Or.inl ⟨hp,h⟩
    · exact Or.inr ⟨hp,h⟩
  · rintro (⟨hp,_⟩ | ⟨hp,_⟩) <;> exact hp

/-- Exact hard overlap word partition into transportable and rigid. -/
theorem hard_overlap_words_eq_transportable_union_rigid
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    hardOverlapCompletionWords C =
      transportableHardOverlapCompletionWords C ∪
        rigidHardOverlapCompletionWords C := by
  classical
  unfold hardOverlapCompletionWords
    transportableHardOverlapCompletionWords
    rigidHardOverlapCompletionWords
  rw [hard_overlap_carriers_eq_transportable_union_rigid]
  ext word
  simp only [Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨p, hp | hp, hw⟩
    · left
      exact ⟨p, hp, hw⟩
    · right
      exact ⟨p, hp, hw⟩
  · rintro (⟨p, hp, hw⟩ | ⟨p, hp, hw⟩)
    · exact ⟨p, Or.inl hp, hw⟩
    · exact ⟨p, Or.inr hp, hw⟩

/-- The two hard-overlap word classes are also DISJOINT:
one Boolean word has one unique residual carrier. -/
theorem rigid_transportable_hard_overlap_words_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Disjoint (rigidHardOverlapCompletionWords C)
      (transportableHardOverlapCompletionWords C) := by
  classical
  rw [Finset.disjoint_left]
  intro word hrigid hmov
  obtain ⟨p,hp,hpw⟩ := Finset.mem_biUnion.mp hrigid
  obtain ⟨q,hq,hqw⟩ := Finset.mem_biUnion.mp hmov
  have hpdata := (mem_rigidHardOverlapCarrierPairs C p).1 hp
  have hqdata := (mem_transportableHardOverlapCarrierPairs C q).1 hq
  have hporder : p.1 < p.2 :=
    ((mem_residualCarrierPairs C p.1 p.2).1
      ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1 hpdata.1).1).1).1
  have hqorder : q.1 < q.2 :=
    ((mem_residualCarrierPairs C q.1 q.2).1
      ((mem_overlapCarrierPairs C q).1
        ((mem_hardOverlapCarrierPairs C q).1 hqdata.1).1).1).1
  obtain ⟨hl,hr⟩ :=
    completion_word_unique_ordered_pair C hporder hqorder
      (Finset.mem_inter.mp hpw).1
      (Finset.mem_inter.mp hpw).2
      (Finset.mem_inter.mp hqw).1
      (Finset.mem_inter.mp hqw).2
  have hpq : p = q := Prod.ext hl hr
  exact hpdata.2 (by simpa [hpq] using hqdata.2)

/-- The hard-overlap mass decomposes EXACTLY, without overlaps
between the two independent failure classes. -/
theorem hard_overlap_card_eq_transportable_add_rigid
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (hardOverlapCompletionWords C).card =
      (transportableHardOverlapCompletionWords C).card +
        (rigidHardOverlapCompletionWords C).card := by
  rw [hard_overlap_words_eq_transportable_union_rigid]
  have h := rigid_transportable_hard_overlap_words_disjoint C
  exact Finset.card_union_of_disjoint h.symm

/-- The rigid overlap mass equals the SUM of full upper
projected Boolean cube masses, with no duplicate word charges. -/
theorem rigid_hard_overlap_card_eq_sum_upper_cubes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (rigidHardOverlapCompletionWords C).card =
      ∑ p ∈ rigidHardOverlapCarrierPairs C,
        2 ^ projectedFree C p.2 := by
  classical
  have hpair :
      ((rigidHardOverlapCarrierPairs C : Finset (V × V)) :
        Set (V × V)).PairwiseDisjoint (carrierOverlapWords C) := by
    intro p hp q hq hpq
    apply carrierOverlapWords_pairwiseDisjoint C
    · have hp0 := ((mem_rigidHardOverlapCarrierPairs C p).1
        (by simpa using hp)).1
      exact ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1 hp0).1).1
    · have hq0 := ((mem_rigidHardOverlapCarrierPairs C q).1
        (by simpa using hq)).1
      exact ((mem_overlapCarrierPairs C q).1
        ((mem_hardOverlapCarrierPairs C q).1 hq0).1).1
    · exact hpq
  unfold rigidHardOverlapCompletionWords
  rw [Finset.card_biUnion hpair]
  apply Finset.sum_congr rfl
  intro p hp
  have hdata := (mem_rigidHardOverlapCarrierPairs C p).1 hp
  have hsame := ((mem_hardOverlapCarrierPairs C p).1 hdata.1).2
  exact hard_no_transport_inter_card_eq_projected_cube
    C hsame hdata.2

/-- A rigid face with strictly LESS projected-free dimension
upstairs is paid ENTIRELY by the lower endpoint's surplus,
as long as that lower endpoint has one strict dyadic layer. -/
theorem rigid_hard_overlap_paid_by_lower_surplus_of_strict_dimension
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {a v : V}
    (hsame : SameRetained C a v)
    (hno : ¬ HasOutgoingHardTransport C a v)
    (hfree : projectedFree C v < projectedFree C a)
    (hlower : exponent a < projectedFree C a) :
    (retainedCompletionWords C a ∩
      retainedCompletionWords C v).card ≤
        dyadicProfileSurplus exponent (projectedFree C) a := by
  rw [hard_no_transport_inter_card_eq_projected_cube C hsame hno]
  have hdim : projectedFree C v ≤ projectedFree C a - 1 := by omega
  have hpow := Nat.pow_le_pow_right
    (by norm_num : (0 : ℕ) < 2) hdim
  have hhalf := half_pow_le_dyadic_surplus_of_lt hlower
  unfold dyadicProfileSurplus
  exact hpow.trans hhalf

#print axioms hard_overlap_words_eq_transportable_union_rigid
#print axioms rigid_transportable_hard_overlap_words_disjoint
#print axioms hard_overlap_card_eq_transportable_add_rigid
#print axioms rigid_hard_overlap_card_eq_sum_upper_cubes
#print axioms rigid_hard_overlap_paid_by_lower_surplus_of_strict_dimension

end OrderedEdgeColoring
end JSP000404Research
