import Mathlib.Tactic

/-!
# Irredundant phase covers and private phases

The phase-cover route should never count all obstruction intervals: highly
overlapping obstructions can be arbitrarily redundant.  The right finite
object is an inclusion-irredundant subcover.

This file isolates two purely combinatorial facts.

* Every member of an irredundant finite cover has a private phase, covered by
  that member and by no other member of the chosen cover.
* For real intervals, private phases forbid nesting.  Consequently, inside an
  irredundant interval family, ordering intervals by left endpoint also
  strictly orders their right endpoints.

The remaining JSP-000404 geometry may therefore work only with the ordered
private obstructions of a minimal cover, rather than with the full critical
family.
-/

namespace JSP000404Research

/-- A finite family of predicates covers the whole phase type. -/
def PredicateCovers
    {I Phase : Type*}
    (A : I → Phase → Prop) (S : Finset I) : Prop :=
  ∀ x : Phase, ∃ i, i ∈ S ∧ A i x

/-- No member of the finite cover can be deleted while preserving coverage. -/
def IrredundantCover
    {I Phase : Type*} [DecidableEq I]
    (A : I → Phase → Prop) (S : Finset I) : Prop :=
  PredicateCovers A S ∧
    ∀ i, i ∈ S → ¬ PredicateCovers A (S.erase i)

/-- Every finite cover contains an inclusion-irredundant subcover.  We choose
a subcover with minimal cardinality and observe that deleting any one of its
members would contradict that minimality. -/
theorem exists_irredundant_subcover
    {I Phase : Type*} [DecidableEq I]
    (A : I → Phase → Prop) (S : Finset I)
    (hcover : PredicateCovers A S) :
    ∃ T : Finset I, T ⊆ S ∧ IrredundantCover A T := by
  classical
  let P : ℕ → Prop := fun m =>
    ∃ T : Finset I,
      T ⊆ S ∧ PredicateCovers A T ∧ T.card = m
  have hP : ∃ m, P m := by
    refine ⟨S.card, S, ?_, hcover, rfl⟩
    intro x hx
    exact hx
  let m : ℕ := Nat.find hP
  have hm : P m := by
    simpa [m] using Nat.find_spec hP
  obtain ⟨T, hTS, hTCover, hTcard⟩ := hm
  refine ⟨T, hTS, hTCover, ?_⟩
  intro i hi hEraseCover
  have hEraseSub : T.erase i ⊆ S :=
    (Finset.erase_subset i T).trans hTS
  have hEraseP : P (T.erase i).card :=
    ⟨T.erase i, hEraseSub, hEraseCover, rfl⟩
  have hmin :
      m ≤ (T.erase i).card := by
    dsimp [m]
    exact Nat.find_min' hP hEraseP
  have hlt :
      (T.erase i).card < m := by
    rw [← hTcard]
    exact Finset.card_erase_lt_of_mem hi
  omega

/-- Every member of an irredundant finite cover owns a private phase. -/
theorem exists_private_phase_of_irredundant
    {I Phase : Type*} [DecidableEq I]
    (A : I → Phase → Prop) (S : Finset I)
    (hmin : IrredundantCover A S)
    {i : I} (hi : i ∈ S) :
    ∃ x : Phase,
      A i x ∧
      ∀ j, j ∈ S → j ≠ i → ¬ A j x := by
  classical
  have hnot := hmin.2 i hi
  unfold PredicateCovers at hnot
  push_neg at hnot
  obtain ⟨x, hx⟩ := hnot
  obtain ⟨j, hjS, hjA⟩ := hmin.1 x
  have hji : j = i := by
    by_contra hne
    have hjErase : j ∈ S.erase i := by
      exact Finset.mem_erase.mpr ⟨hne, hjS⟩
    exact (hx j hjErase) hjA
  subst j
  refine ⟨x, hjA, ?_⟩
  intro j hjS hji hjA'
  have hjErase : j ∈ S.erase i := by
    exact Finset.mem_erase.mpr ⟨hji, hjS⟩
  exact (hx j hjErase) hjA'

/-- Private phases attached to two different cover members are distinct. -/
theorem private_phases_ne
    {I Phase : Type*}
    (A : I → Phase → Prop)
    {i j : I} {x y : Phase}
    (hij : i ≠ j)
    (hxi : A i x)
    (hxprivate : ¬ A j x)
    (hyj : A j y) :
    x ≠ y := by
  intro hxy
  subst y
  exact hxprivate hyj

/-- Closed real interval carried by one obstruction. -/
def InClosedInterval
    {I : Type*}
    (L R : I → ℝ) (i : I) (x : ℝ) : Prop :=
  L i ≤ x ∧ x ≤ R i

/-- A private point for interval j rules out containment of j in a distinct
interval i of the same irredundant family. -/
theorem not_interval_contained_of_private
    {I : Type*}
    (L R : I → ℝ)
    {i j : I} {x : ℝ}
    (hij : i ≠ j)
    (hxj : InClosedInterval L R j x)
    (hxprivate : ¬ InClosedInterval L R i x) :
    ¬ (L i ≤ L j ∧ R j ≤ R i) := by
  rintro ⟨hL, hR⟩
  apply hxprivate
  exact ⟨hL.trans hxj.1, hxj.2.trans hR⟩

/-- Hence, for two different intervals in a private-point family, weak order
of left endpoints forces strict order of right endpoints. -/
theorem right_strictMono_of_left_le_of_private
    {I : Type*}
    (L R : I → ℝ)
    {i j : I} {x : ℝ}
    (hij : i ≠ j)
    (hL : L i ≤ L j)
    (hxj : InClosedInterval L R j x)
    (hxprivate : ¬ InClosedInterval L R i x) :
    R i < R j := by
  by_contra hnot
  have hR : R j ≤ R i := le_of_not_gt hnot
  exact (not_interval_contained_of_private
    L R hij hxj hxprivate) ⟨hL, hR⟩

/-- Irredundant real-interval covers have no nesting: once left endpoints are
ordered, right endpoints are strictly ordered as well. -/
theorem irredundant_interval_right_strict
    {I : Type*} [DecidableEq I]
    (L R : I → ℝ) (S : Finset I)
    (hmin : IrredundantCover (InClosedInterval L R) S)
    {i j : I}
    (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j)
    (hL : L i ≤ L j) :
    R i < R j := by
  obtain ⟨x, hxj, hxprivate⟩ :=
    exists_private_phase_of_irredundant
      (InClosedInterval L R) S hmin hj
  exact right_strictMono_of_left_le_of_private
    L R hij hL hxj (hxprivate i hi hij.symm)

/-- Two distinct intervals in an irredundant interval cover cannot be
comparable by containment in either direction. -/
theorem irredundant_intervals_not_nested
    {I : Type*} [DecidableEq I]
    (L R : I → ℝ) (S : Finset I)
    (hmin : IrredundantCover (InClosedInterval L R) S)
    {i j : I}
    (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    ¬ ((L i ≤ L j ∧ R j ≤ R i) ∨
       (L j ≤ L i ∧ R i ≤ R j)) := by
  intro hnested
  rcases hnested with hijContain | hjiContain
  · obtain ⟨x, hxj, hxprivate⟩ :=
      exists_private_phase_of_irredundant
        (InClosedInterval L R) S hmin hj
    exact (not_interval_contained_of_private
      L R hij hxj (hxprivate i hi hij.symm)) hijContain
  · obtain ⟨x, hxi, hxprivate⟩ :=
      exists_private_phase_of_irredundant
        (InClosedInterval L R) S hmin hi
    exact (not_interval_contained_of_private
      L R hij.symm hxi (hxprivate j hj hij)) hjiContain

/-- Abstract slot-compression principle: if every pair of intervals assigned
to the same slot is nested, then the slot map is injective on any
irredundant subcover. -/
theorem slot_injective_on_irredundant_of_nested_fibres
    {I Slot : Type*} [DecidableEq I]
    (L R : I → ℝ) (slot : I → Slot)
    (S : Finset I)
    (hmin : IrredundantCover (InClosedInterval L R) S)
    (hnested :
      ∀ {i j : I}, slot i = slot j →
        (L i ≤ L j ∧ R j ≤ R i) ∨
        (L j ≤ L i ∧ R i ≤ R j)) :
    ∀ {i j : I}, i ∈ S → j ∈ S →
      slot i = slot j → i = j := by
  intro i j hi hj hslot
  by_contra hij
  exact (irredundant_intervals_not_nested
    L R S hmin hi hj hij) (hnested hslot)

/-- Finite-slot cardinality version of the nested-fibre compression. -/
theorem irredundant_card_le_slots_of_nested_fibres
    {I Slot : Type*} [DecidableEq I] [Fintype Slot]
    (L R : I → ℝ) (slot : I → Slot)
    (S : Finset I)
    (hmin : IrredundantCover (InClosedInterval L R) S)
    (hnested :
      ∀ {i j : I}, slot i = slot j →
        (L i ≤ L j ∧ R j ≤ R i) ∨
        (L j ≤ L i ∧ R i ≤ R j)) :
    S.card ≤ Fintype.card Slot := by
  classical
  let f : {i : I // i ∈ S} → Slot := fun i => slot i.1
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact slot_injective_on_irredundant_of_nested_fibres
      L R slot S hmin hnested i.2 j.2 hij
  have hcard := Fintype.card_le_of_injective f hf
  simpa [f] using hcard

#print axioms irredundant_intervals_not_nested
#print axioms slot_injective_on_irredundant_of_nested_fibres
#print axioms irredundant_card_le_slots_of_nested_fibres

#print axioms exists_irredundant_subcover
#print axioms exists_private_phase_of_irredundant
#print axioms private_phases_ne
#print axioms not_interval_contained_of_private
#print axioms right_strictMono_of_left_le_of_private
#print axioms irredundant_interval_right_strict

end JSP000404Research
