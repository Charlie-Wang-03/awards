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
  let P : ℕ → Prop := fun m =>
    ∃ T : Finset V,
      T ⊆ S ∧
      BlockDeficient demand blocks T ∧
      T.card = m
  have hP : ∃ m, P m := by
    refine ⟨S.card,S,Finset.Subset.rfl,hS,rfl⟩
  let m := Nat.find hP
  have hm : P m := Nat.find_spec hP
  obtain ⟨T,hTS,hTdef,hTcard⟩ := hm
  refine ⟨T,hTS,hTdef,?_⟩
  intro U hUT hUdef
  have hUS : U ⊆ S := hUT.1.trans hTS
  have hPU : P U.card := ⟨U,hUS,hUdef,rfl⟩
  have hmle : m ≤ U.card := Nat.find_min' hP hPU
  have hlt : U.card < T.card := Finset.card_lt_card hUT
  rw [hTcard] at hlt
  omega

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
