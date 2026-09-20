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

#print axioms exists_private_phase_of_irredundant
#print axioms private_phases_ne
#print axioms not_interval_contained_of_private
#print axioms right_strictMono_of_left_le_of_private
#print axioms irredundant_interval_right_strict

end JSP000404Research
