import Mathlib.Data.Finset.Lattice
import Mathlib.Tactic

/-!
# Inclusion-minimal deficient block family

For a finite family of candidate blocks B(v) with integer demands d(v), define
a vertex subset S to be deficient when

  card (biUnion S B) < sum_{v in S} d(v).

Any deficient finite set contains an inclusion-minimal deficient subset T.
Such a T has the exact deletion property:

  for every v in T,
    sum_{u in T.erase v} d(u)
      <= card (biUnion (T.erase v) B).

This is the canonical Hall-obstruction object for the remaining all-N proof.
It allows the geometric transition machinery to be applied under a
minimality hypothesis rather than to arbitrary subsets.
-/

namespace JSP000404Research

def BlockDeficient
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    (S : Finset V) : Prop :=
  (S.biUnion blocks).card <
    ∑ v ∈ S, demand v

theorem exists_minimal_deficient_subset
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {S : Finset V}
    (hS : BlockDeficient demand blocks S) :
    ∃ T : Finset V,
      T ⊆ S ∧
      BlockDeficient demand blocks T ∧
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient demand blocks U := by
  classical
  let candidates :=
    (S.powerset).filter
      (fun T => BlockDeficient demand blocks T)
  have hnonempty : candidates.Nonempty := by
    refine ⟨S,?_⟩
    simp [candidates,hS]
  let T := candidates.min' hnonempty
  have hTmem : T ∈ candidates := Finset.min'_mem _ _
  have hTdata := Finset.mem_filter.mp hTmem
  refine ⟨T,?_,hTdata.2,?_⟩
  · exact Finset.mem_powerset.mp hTdata.1
  · intro U hUT hUdef
    have hUS : U ⊆ S :=
      hUT.1.trans (Finset.mem_powerset.mp hTdata.1)
    have hUmem : U ∈ candidates := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr hUS,hUdef⟩
    have hle : T ≤ U :=
      Finset.min'_le candidates U hUmem
    exact (not_le_of_gt (Finset.card_lt_card hUT)) hle

theorem minimal_deficient_delete_recovers
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {T : Finset V}
    (hdef : BlockDeficient demand blocks T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient demand blocks U) :
    ∀ v ∈ T,
      (∑ u ∈ T.erase v, demand u)
        ≤
      ((T.erase v).biUnion blocks).card := by
  intro v hv
  have hproper : T.erase v ⊂ T := by
    constructor
    · exact Finset.erase_subset _ _
    · intro heq
      have : v ∉ T.erase v := by simp
      rw [heq] at this
      exact this hv
  have hnot := hmin (T.erase v) hproper
  unfold BlockDeficient at hnot
  omega

theorem deficient_set_nonempty_of_positive_demands
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    (hpos : ∀ v, 0 < demand v)
    {T : Finset V}
    (hdef : BlockDeficient demand blocks T) :
    T.Nonempty := by
  by_contra h
  have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  subst T
  simp [BlockDeficient] at hdef

#print axioms exists_minimal_deficient_subset
#print axioms minimal_deficient_delete_recovers
#print axioms deficient_set_nonempty_of_positive_demands

end JSP000404Research
