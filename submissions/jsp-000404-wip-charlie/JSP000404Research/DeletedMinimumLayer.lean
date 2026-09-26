
import JSP000404Research.ExactAngleWitnessRestriction
import JSP000404Research.SecondDeletionTwoStableMinima
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Minimum layers under one vertex deletion

This file is purely finite/combinatorial.  It identifies the minimum exponent
layer in the deleted subtype with the old minimum layer with the deleted
vertex removed.

Consequently a root minimum layer of cardinality at least five leaves at least
four minimum vertices after deleting one minimum.  The second-deletion slack
theorem can then be applied directly on the deleted subtype.
-/

namespace JSP000404Research

def deletedExponent
    {V : Type*}
    (exponent : V → ℕ)
    (r : V) :
    DeletedVertex r → ℕ :=
  fun v => exponent v.1

def deletedVertexEmbedding
    {V : Type*}
    (r : V) :
    DeletedVertex r ↪ V where
  toFun := fun v => v.1
  inj' := by
    intro u v h
    exact Subtype.ext h

/-- The deleted-subtype exponent layer maps exactly to the old layer with r
removed. -/
theorem map_deleted_exponentLayer_eq_erase
    {V : Type*} [Fintype V] [DecidableEq V]
    (exponent : V → ℕ)
    (r : V)
    (a : ℕ)
    (hr : exponent r = a) :
    (exponentLayer (deletedExponent exponent r) a).map
        (deletedVertexEmbedding r)
      =
    (exponentLayer exponent a).erase r := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
    have hwExp :
        exponent w.1 = a := by
      exact (mem_exponentLayer
        (deletedExponent exponent r) a w).1 hw
    apply Finset.mem_erase.mpr
    exact ⟨w.2, (mem_exponentLayer exponent a w.1).2 hwExp⟩
  · intro hv
    have hv' := Finset.mem_erase.mp hv
    let w : DeletedVertex r := ⟨v, hv'.1⟩
    apply Finset.mem_map.mpr
    refine ⟨w, ?_, rfl⟩
    apply (mem_exponentLayer
      (deletedExponent exponent r) a w).2
    exact (mem_exponentLayer exponent a v).1 hv'.2

/-- Exact cardinality relation for one deleted minimum vertex. -/
theorem deleted_exponentLayer_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (exponent : V → ℕ)
    (r : V)
    (a : ℕ)
    (hr : exponent r = a) :
    (exponentLayer (deletedExponent exponent r) a).card =
      (exponentLayer exponent a).card - 1 := by
  classical
  have hmap :=
    congrArg Finset.card
      (map_deleted_exponentLayer_eq_erase
        exponent r a hr)
  have hrM :
      r ∈ exponentLayer exponent a := by
    exact (mem_exponentLayer exponent a r).2 hr
  simp only [Finset.card_map] at hmap
  rw [Finset.card_erase_of_mem hrM] at hmap
  exact hmap

/-- Five root minima leave at least four minima in the deleted subtype. -/
theorem four_le_deleted_minimum_layer_of_five_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (exponent : V → ℕ)
    (r : V)
    (a : ℕ)
    (hr : exponent r = a)
    (hfive :
      5 ≤ (exponentLayer exponent a).card) :
    4 ≤
      (exponentLayer
        (deletedExponent exponent r) a).card := by
  rw [deleted_exponentLayer_card exponent r a hr]
  omega

/-- Subtype-compatible second-deletion outlet.

After deleting one minimum r, suppose the child exponent profile is just the
restricted old profile, has exact total mass 2^n, and a second minimum s has
a bounded monotone deletion column.  If the old minimum layer had at least
five vertices, then two distinct child minima survive s with no unit gain.
-/
theorem exists_two_deleted_minima_without_second_gain
    {V : Type*} [Fintype V] [DecidableEq V]
    (exponent : V → ℕ)
    (afterChild :
      DeletedVertex r → DeletedVertex r → ℕ)
    (n a : ℕ)
    (r s : V)
    (hr : exponent r = a)
    (hs : exponent s = a)
    (hrs : r ≠ s)
    (hfive :
      5 ≤ (exponentLayer exponent a).card)
    (htotal :
      (∑ x : DeletedVertex r,
        2 ^ deletedExponent exponent r x) = 2 ^ n)
    (hmono :
      ∀ x : DeletedVertex r,
        x ≠ ⟨s, Ne.symm hrs⟩ →
        deletedExponent exponent r x ≤
          afterChild ⟨s, Ne.symm hrs⟩ x)
    (hpost :
      deletionPostWeight afterChild
        ⟨s, Ne.symm hrs⟩ ≤ 2 ^ n) :
    ∃ j k : DeletedVertex r,
      j ≠ k ∧
      j ≠ ⟨s, Ne.symm hrs⟩ ∧
      k ≠ ⟨s, Ne.symm hrs⟩ ∧
      exponent j.1 = a ∧
      exponent k.1 = a ∧
      ¬ exponent j.1 + 1 ≤
        afterChild ⟨s, Ne.symm hrs⟩ j ∧
      ¬ exponent k.1 + 1 ≤
        afterChild ⟨s, Ne.symm hrs⟩ k := by
  let sChild : DeletedVertex r :=
    ⟨s, Ne.symm hrs⟩
  have hsChild :
      deletedExponent exponent r sChild = a := by
    simpa [deletedExponent, sChild] using hs
  have hfour :
      4 ≤
        (exponentLayer
          (deletedExponent exponent r) a).card :=
    four_le_deleted_minimum_layer_of_five_le
      exponent r a hr hfive
  obtain ⟨j, k, hjk, hjs, hks,
      hjExp, hkExp, hjNo, hkNo⟩ :=
    exists_two_minimum_survivors_without_second_gain
      (deletedExponent exponent r)
      afterChild n a sChild
      htotal hsChild
      (by simpa [sChild] using hmono)
      (by simpa [sChild] using hpost)
      hfour
  refine ⟨j, k, hjk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [sChild] using hjs
  · simpa [sChild] using hks
  · simpa [deletedExponent] using hjExp
  · simpa [deletedExponent] using hkExp
  · simpa [deletedExponent, sChild] using hjNo
  · simpa [deletedExponent, sChild] using hkNo

#print axioms map_deleted_exponentLayer_eq_erase
#print axioms deleted_exponentLayer_card
#print axioms four_le_deleted_minimum_layer_of_five_le
#print axioms exists_two_deleted_minima_without_second_gain

end JSP000404Research
