import JSP000404Research.CriticalPhaseInterval
import JSP000404Research.MinimalPhaseCover
import Mathlib.Tactic

/-!
# Domain-restricted critical interval covers

CAUTION: A finite family of bounded closed intervals cannot cover ALL
of Real. IrredundantCover (CriticalBadAt ...) S demands precisely such
global coverage and must not be used to claim a non-vacuous phase cover.

Instead fix a prescribed phase-domain predicate Domain : Real -> Prop.
Only phases inside Domain must be covered. The following construction
extracts private phases IN Domain, forbids nested chosen intervals, and
proves anchor/slot injection without assuming coverage of the full line.

Still missing for JSP-000404: proving that the physically relevant
phase-domain is covered by concrete AngleCap critical obstructions and
that its slot owners pay the final dyadic debts with no reuse.
-/

namespace JSP000404Research

def PredicateCoversOn
    {I Phase : Type*}
    (Domain : Phase → Prop) (A : I → Phase → Prop)
    (S : Finset I) : Prop :=
  ∀ x, Domain x → ∃ i, i ∈ S ∧ A i x

def IrredundantCoverOn
    {I Phase : Type*} [DecidableEq I]
    (Domain : Phase → Prop) (A : I → Phase → Prop)
    (S : Finset I) : Prop :=
  PredicateCoversOn Domain A S ∧
    ∀ i, i ∈ S → ¬ PredicateCoversOn Domain A (S.erase i)

/-- Every finite restricted-domain cover contains an irredundant
restricted subcover. The global cover theorem is used ONLY on the
subtype of phases in the domain, not on the whole real line. -/
theorem exists_irredundant_subcover_on
    {I Phase : Type*} [DecidableEq I]
    (Domain : Phase → Prop) (A : I → Phase → Prop)
    (S : Finset I)
    (hcover : PredicateCoversOn Domain A S) :
    ∃ T : Finset I, T ⊆ S ∧ IrredundantCoverOn Domain A T := by
  classical
  let B : I → {x : Phase // Domain x} → Prop :=
    fun i x => A i x.1
  have hcoverSub : PredicateCovers B S := by
    intro x
    exact hcover x.1 x.2
  obtain ⟨T, hTS, hmin⟩ :=
    exists_irredundant_subcover B S hcoverSub
  refine ⟨T, hTS, ?_, ?_⟩
  · intro x hx
    exact hmin.1 ⟨x, hx⟩
  · intro i hi hErase
    apply hmin.2 i hi
    intro x
    exact hErase x.1 x.2

/-- A minimal cover of a restricted phase-domain provides a private
phase within that domain for each selected obstruction. -/
theorem exists_private_phase_of_irredundant_on
    {I Phase : Type*} [DecidableEq I]
    (Domain : Phase → Prop) (A : I → Phase → Prop)
    (S : Finset I)
    (hmin : IrredundantCoverOn Domain A S)
    {i : I} (hi : i ∈ S) :
    ∃ x, Domain x ∧ A i x ∧
      ∀ j, j ∈ S → j ≠ i → ¬ A j x := by
  classical
  have hnot := hmin.2 i hi
  unfold PredicateCoversOn at hnot
  push_neg at hnot
  obtain ⟨x, hxDomain, hx⟩ := hnot
  obtain ⟨j, hjS, hjA⟩ := hmin.1 x hxDomain
  have hji : j = i := by
    by_contra hne
    have hjErase : j ∈ S.erase i :=
      Finset.mem_erase.mpr ⟨hne, hjS⟩
    exact (hx j hjErase) hjA
  subst j
  refine ⟨x, hxDomain, hjA, ?_⟩
  intro j hjS hji hjA
  exact (hx j (Finset.mem_erase.mpr ⟨hji, hjS⟩)) hjA

/-- A restricted-domain irredundant interval family contains no
nested pair of distinct selected intervals. -/
theorem irredundant_on_intervals_not_nested
    {I : Type*} [DecidableEq I]
    (Domain : ℝ → Prop)
    (L R : I → ℝ) (S : Finset I)
    (hmin : IrredundantCoverOn Domain (InClosedInterval L R) S)
    {i j : I} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    ¬ ((L i ≤ L j ∧ R j ≤ R i) ∨
       (L j ≤ L i ∧ R i ≤ R j)) := by
  intro hnested
  rcases hnested with hijContain | hjiContain
  · obtain ⟨x, _, hxj, hxprivate⟩ :=
      exists_private_phase_of_irredundant_on
        Domain (InClosedInterval L R) S hmin hj
    exact (not_interval_contained_of_private
      L R hij hxj (hxprivate i hi hij)) hijContain
  · obtain ⟨x, _, hxi, hxprivate⟩ :=
      exists_private_phase_of_irredundant_on
        Domain (InClosedInterval L R) S hmin hi
    exact (not_interval_contained_of_private
      L R hij.symm hxi (hxprivate j hj hij.symm)) hjiContain

/-- The shared-right-endpoint property of critical bad intervals
implies injectivity of their anchors on every NONVACUOUS restricted-
domain irredundant cover. No global real-line cover is assumed. -/
theorem critical_anchor_injective_of_irredundant_on
    {I : Type*} [DecidableEq I]
    (Domain : ℝ → Prop)
    (alpha s : I → ℝ) (delta : ℝ)
    (S : Finset I)
    (hmin : IrredundantCoverOn Domain
       (fun i x => criticalBadLeft (alpha i) (s i) ≤ x ∧
          x ≤ criticalBadRight (alpha i) delta) S) :
    ∀ {i j : I}, i ∈ S → j ∈ S →
      alpha i = alpha j → i = j := by
  intro i j hi hj hanchor
  by_contra hij
  let L : I → ℝ := fun k => criticalBadLeft (alpha k) (s k)
  let R : I → ℝ := fun k => criticalBadRight (alpha k) delta
  have hmin' : IrredundantCoverOn Domain (InClosedInterval L R) S := by
    change IrredundantCoverOn Domain (InClosedInterval L R) S at hmin
    exact hmin
  have hR : R i = R j := by
    dsimp [R]
    rw [hanchor]
  have hnested :=
    irredundant_on_intervals_not_nested
      Domain L R S hmin' hi hj hij
  rcases le_total (L i) (L j) with hL | hL
  · apply hnested
    exact Or.inl ⟨hL, hR.ge⟩
  · apply hnested
    exact Or.inr ⟨hL, hR.le⟩

/-- If same-slot obstructions have the same anchor, the restricted
critical cover cannot reuse a slot. -/
theorem critical_irredundant_on_card_le_slots
    {I Slot : Type*} [DecidableEq I] [Fintype Slot]
    (Domain : ℝ → Prop) (alpha s : I → ℝ)
    (delta : ℝ) (slot : I → Slot) (S : Finset I)
    (hmin : IrredundantCoverOn Domain
       (fun i x => criticalBadLeft (alpha i) (s i) ≤ x ∧
          x ≤ criticalBadRight (alpha i) delta) S)
    (hslot : ∀ {i j : I}, slot i = slot j → alpha i = alpha j) :
    S.card ≤ Fintype.card Slot := by
  classical
  let f : {i : I // i ∈ S} → Slot := fun i => slot i.1
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply critical_anchor_injective_of_irredundant_on
      Domain alpha s delta S hmin i.2 j.2
    exact hslot hij
  have hcard := Fintype.card_le_of_injective f hf
  simpa [f] using hcard

#print axioms exists_irredundant_subcover_on
#print axioms exists_private_phase_of_irredundant_on
#print axioms irredundant_on_intervals_not_nested
#print axioms critical_anchor_injective_of_irredundant_on
#print axioms critical_irredundant_on_card_le_slots

end JSP000404Research
