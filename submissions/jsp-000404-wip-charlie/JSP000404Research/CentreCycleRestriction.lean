import JSP000404Research.CanonicalRayRestriction
import JSP000404Research.CentreProjectiveCycle
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

/-!
# Restricting a concrete centre projective cycle after deleting another vertex

CanonicalRayRestriction identifies the child non-centre vertices with the
parent rays other than the deleted vertex and proves that their canonical
rho/sign/theta data are unchanged.

This file lifts that pointwise equivalence to an actual CentreProjectiveCycle:
filter the deleted ray out of the parent sorted ray list and transport every
remaining ray through the child/parent equivalence.

The resulting child list is complete, duplicate-free, and theta-sorted.  Thus
the geometric deletion problem is reduced to a list-level deletion of one
entry from the parent cyclic ray list.
-/

namespace JSP000404Research

/-- Partial transport of one parent ray into the deleted configuration. -/
noncomputable def parentRayToChildOption
    {V : Type*}
    (r i : V) (hir : i ≠ r)
    (j : OtherVertex i) :
    Option (OtherVertex (survivingCentre r i hir)) :=
  if hjr : j.1 ≠ r then
    some ((childOtherEquivParentSurvivor r i hir).symm
      ⟨j, hjr⟩)
  else
    none

/-- Transporting a genuine child ray to the parent and back returns the child. -/
@[simp] theorem parentRayToChildOption_childOtherToParent
    {V : Type*}
    (r i : V) (hir : i ≠ r)
    (j : OtherVertex (survivingCentre r i hir)) :
    parentRayToChildOption r i hir
        (childOtherToParent r i hir j)
      =
    some j := by
  have hnr :=
    childOtherToParent_ne_deleted r i hir j
  unfold parentRayToChildOption
  simp only [dif_pos hnr]
  congr 1
  exact (childOtherEquivParentSurvivor r i hir).symm_apply_apply j

/-- The parent image of every successful partial transport is the original
parent ray. -/
theorem parent_of_parentRayToChildOption_eq_some
    {V : Type*}
    (r i : V) (hir : i ≠ r)
    {a : OtherVertex i}
    {b : OtherVertex (survivingCentre r i hir)}
    (h : parentRayToChildOption r i hir a = some b) :
    childOtherToParent r i hir b = a := by
  unfold parentRayToChildOption at h
  split at h
  next ha =>
    have hb :
        (childOtherEquivParentSurvivor r i hir).symm
            ⟨a, ha⟩ = b := by
      simpa using Option.some.inj h
    have hback :=
      congrArg
        (childOtherEquivParentSurvivor r i hir)
        hb
    simpa using hback
  next ha =>
    simp at h

/-- Child ray list obtained by filtering the deleted parent ray. -/
noncomputable def restrictedRayList
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (r : V) (hir : i ≠ r) :
    List (OtherVertex (survivingCentre r i hir)) :=
  C.rays.filterMap (parentRayToChildOption r i hir)

/-- Every child ray occurs in the transported list. -/
theorem mem_restrictedRayList
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (r : V) (hir : i ≠ r)
    (j : OtherVertex (survivingCentre r i hir)) :
    j ∈ restrictedRayList C r hir := by
  rw [restrictedRayList, List.mem_filterMap]
  refine ⟨childOtherToParent r i hir j, ?_, ?_⟩
  · exact C.mem_rays_iff _
  · exact parentRayToChildOption_childOtherToParent
      r i hir j

/-- The transported child ray list is complete. -/
theorem restrictedRayList_complete
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (r : V) (hir : i ≠ r) :
    (restrictedRayList C r hir).toFinset = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro j
  simpa using mem_restrictedRayList C r hir j

/-- The partial ray transport is injective on successful outputs. -/
theorem parentRayToChildOption_injective_on_some
    {V : Type*}
    (r i : V) (hir : i ≠ r) :
    ∀ a a' b,
      b ∈ parentRayToChildOption r i hir a →
      b ∈ parentRayToChildOption r i hir a' →
      a = a' := by
  intro a a' b hba hba'
  have ha :
      childOtherToParent r i hir b = a := by
    apply parent_of_parentRayToChildOption_eq_some
      r i hir
    simpa using hba
  have ha' :
      childOtherToParent r i hir b = a' := by
    apply parent_of_parentRayToChildOption_eq_some
      r i hir
    simpa using hba'
  exact ha.symm.trans ha'

/-- Filtering and transporting preserves duplicate-freeness. -/
theorem restrictedRayList_nodup
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (r : V) (hir : i ≠ r) :
    (restrictedRayList C r hir).Nodup := by
  unfold restrictedRayList
  exact C.nodup.filterMap
    (parentRayToChildOption_injective_on_some
      r i hir)

/-- Theta order is preserved because deletion does not change any surviving
canonical projective theta. -/
theorem restrictedRayList_theta_sorted
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (r : V) (hir : i ≠ r) :
    (restrictedRayList C r hir).Pairwise
      (fun a b =>
        rayThetaAt
            (restrictedPoint_injective hp r)
            (survivingCentre r i hir) a
          ≤
        rayThetaAt
            (restrictedPoint_injective hp r)
            (survivingCentre r i hir) b) := by
  unfold restrictedRayList
  refine C.theta_sorted.filterMap
    (parentRayToChildOption r i hir) ?_
  intro a a' b b' haa' hba hba'
  have hpa :
      childOtherToParent r i hir b = a :=
    parent_of_parentRayToChildOption_eq_some
      r i hir (by simpa using hba)
  have hpa' :
      childOtherToParent r i hir b' = a' :=
    parent_of_parentRayToChildOption_eq_some
      r i hir (by simpa using hba')
  rw [rayThetaAt_restrict_delete hp r i hir b,
      rayThetaAt_restrict_delete hp r i hir b',
      hpa, hpa']
  exact haa'

/-- If the deleted configuration still contains another vertex besides the
surviving centre, the transported list is nonempty. -/
theorem restrictedRayList_nonempty
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (r : V) (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir))) :
    restrictedRayList C r hir ≠ [] := by
  obtain ⟨j⟩ := hother
  intro hnil
  have hj :=
    mem_restrictedRayList C r hir j
  rw [hnil] at hj
  simp at hj

/-- Concrete child projective cycle obtained directly from the parent cycle. -/
noncomputable def CentreProjectiveCycle.restrictDelete
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (r : V) (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir))) :
    CentreProjectiveCycle
      (restrictedPoint_injective hp r)
      (survivingCentre r i hir) where
  rays := restrictedRayList C r hir
  complete := restrictedRayList_complete C r hir
  nodup := restrictedRayList_nodup C r hir
  nonempty := restrictedRayList_nonempty C r hir hother
  theta_sorted := restrictedRayList_theta_sorted C r hir

@[simp] theorem CentreProjectiveCycle.restrictDelete_rays
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (r : V) (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir))) :
    (C.restrictDelete r hir hother).rays =
      restrictedRayList C r hir := rfl

#print axioms parentRayToChildOption_childOtherToParent
#print axioms restrictedRayList_complete
#print axioms restrictedRayList_nodup
#print axioms restrictedRayList_theta_sorted
#print axioms CentreProjectiveCycle.restrictDelete

end JSP000404Research
