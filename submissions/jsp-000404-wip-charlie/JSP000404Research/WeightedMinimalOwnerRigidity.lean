import JSP000404Research.WeightedMinimalHallObstruction
import Mathlib.Tactic

/-!
# Singleton-owner rigidity in a minimal dyadic Hall obstruction

In a minimal deficient set of exploded dyadic target units, deleting any one
unit leaves the target neighbourhood unchanged.

If a vertex v contributes exactly one unit x to the obstruction, deleting x
removes v entirely from the support.  Therefore every word of the whole block
B(v) must still be supplied by a unit belonging to another vertex.

Thus singleton owners are globally covered by the other owner blocks, not just
partially collided.  This is much stronger than the vertex-level
private-word deficit and is especially restrictive for rich projected-loss
Hamming stars.
-/

namespace JSP000404Research

noncomputable def ownerUnits
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (s : Finset (DyadicTargetUnit exponent))
    (v : V) : Finset (DyadicTargetUnit exponent) := by
  classical
  exact s.filter (fun x => x.1 = v)

@[simp] theorem mem_ownerUnits
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (s : Finset (DyadicTargetUnit exponent))
    (v : V)
    (x : DyadicTargetUnit exponent) :
    x ∈ ownerUnits exponent s v ↔
      x ∈ s ∧ x.1 = v := by
  classical
  simp [ownerUnits]

theorem singleton_owner_has_unique_unit
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    {s : Finset (DyadicTargetUnit exponent)}
    {v : V}
    (hcard : (ownerUnits exponent s v).card = 1) :
    ∃! x : DyadicTargetUnit exponent,
      x ∈ s ∧ x.1 = v := by
  classical
  have hnonempty :
      (ownerUnits exponent s v).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨x,hx⟩ := hnonempty
  refine ⟨x,(mem_ownerUnits exponent s v x).1 hx,?_⟩
  intro y hy
  have hyOwner :
      y ∈ ownerUnits exponent s v :=
    (mem_ownerUnits exponent s v y).2 hy
  have hxOwner : x ∈ ownerUnits exponent s v := hx
  have hsub :
      {x,y} ⊆ ownerUnits exponent s v := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxOwner
    · exact hyOwner
  by_contra hxy
  have htwo : ({x,y} : Finset (DyadicTargetUnit exponent)).card = 2 := by
    simp [hxy]
  have hcardTwo :
      2 ≤ (ownerUnits exponent s v).card := by
    rw [← htwo]
    exact Finset.card_le_card hsub
  omega

theorem minimal_unit_obstruction_singleton_owner_block_covered_by_others
    {V : Type*} [Fintype V]
    {n : ℕ}
    (exponent : V → ℕ)
    (blocks : V → Finset (Fin n → Bool))
    {s : Finset (DyadicTargetUnit exponent)}
    (hmin :
      FiniteHall.InclusionMinimalDeficient
        (blockUnitCandidates exponent blocks) s)
    {v : V}
    (howner : (ownerUnits exponent s v).card = 1) :
    blocks v ⊆
      (s.filter (fun x => x.1 ≠ v)).biUnion
        (blockUnitCandidates exponent blocks) := by
  classical
  obtain ⟨x,hxs,hxv,huniq⟩ :=
    singleton_owner_has_unique_unit exponent howner
  have hneighEq :=
    FiniteHall.minimalDeficient_biUnion_erase_eq
      (blockUnitCandidates exponent blocks)
      hmin hxs
  intro word hword
  have hwordAll :
      word ∈ s.biUnion
        (blockUnitCandidates exponent blocks) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hxs,?_⟩
    simpa [blockUnitCandidates,hxv] using hword
  have hwordErase :
      word ∈ (s.erase x).biUnion
        (blockUnitCandidates exponent blocks) := by
    rw [hneighEq]
    exact hwordAll
  obtain ⟨y,hyErase,hyWord⟩ :=
    Finset.mem_biUnion.mp hwordErase
  have hyData := Finset.mem_erase.mp hyErase
  have hyv : y.1 ≠ v := by
    intro h
    have hyOwner : y ∈ s ∧ y.1 = v :=
      ⟨hyData.2,h⟩
    have hyEq := huniq y hyOwner
    exact hyData.1 hyEq
  apply Finset.mem_biUnion.mpr
  refine ⟨y,?_,hyWord⟩
  exact Finset.mem_filter.mpr ⟨hyData.2,hyv⟩

theorem minimal_unit_obstruction_singleton_owner_every_word_crosses_owner
    {V : Type*} [Fintype V]
    {n : ℕ}
    (exponent : V → ℕ)
    (blocks : V → Finset (Fin n → Bool))
    {s : Finset (DyadicTargetUnit exponent)}
    (hmin :
      FiniteHall.InclusionMinimalDeficient
        (blockUnitCandidates exponent blocks) s)
    {v : V}
    (howner : (ownerUnits exponent s v).card = 1) :
    ∀ word ∈ blocks v,
      ∃ y ∈ s,
        y.1 ≠ v ∧
        word ∈ blocks y.1 := by
  intro word hword
  have hcovered :=
    minimal_unit_obstruction_singleton_owner_block_covered_by_others
      exponent blocks hmin howner hword
  obtain ⟨y,hy,hwordY⟩ := Finset.mem_biUnion.mp hcovered
  have hyData := Finset.mem_filter.mp hy
  exact ⟨y,hyData.2,hwordY⟩

#print axioms minimal_unit_obstruction_singleton_owner_block_covered_by_others
#print axioms minimal_unit_obstruction_singleton_owner_every_word_crosses_owner

end JSP000404Research
