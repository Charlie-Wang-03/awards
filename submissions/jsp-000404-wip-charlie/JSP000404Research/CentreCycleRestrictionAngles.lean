import JSP000404Research.CentreCycleRestriction
import JSP000404Research.PinnedCycleRotation
import Mathlib.Tactic

/-!
# Angle-list form of centre-cycle restriction

After deleting another vertex r from a surviving centre i, the concrete child
cycle constructed in CentreCycleRestriction is obtained by removing exactly
the parent ray i--r.

This file states that fact directly on angle lists.

If the parent ray list is

  pre ++ deletedRay :: post,

then the restricted child angle list is

  map theta pre ++ map theta post.

All canonical theta values are unchanged by restriction, so no geometric
information remains hidden in the subtype transport.
-/

namespace JSP000404Research

/-- The parent ray from i to the vertex r which is about to be deleted. -/
def deletedParentRay
    {V : Type*}
    (r i : V) (hir : i ≠ r) :
    OtherVertex i :=
  ⟨r, hir.symm⟩

@[simp] theorem deletedParentRay_val
    {V : Type*}
    (r i : V) (hir : i ≠ r) :
    (deletedParentRay r i hir).1 = r := rfl

/-- Parent theta, unless the ray is exactly the deleted ray. -/
noncomputable def parentAngleAfterDeleteOption
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (r i : V)
    (j : OtherVertex i) : Option ℝ :=
  if hjr : j.1 ≠ r then
    some (rayThetaAt hp i j)
  else
    none

/-- Mapping the transported child theta through the partial ray transport is
exactly the parent theta filter. -/
theorem parentRayToChildOption_map_theta
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (r i : V) (hir : i ≠ r)
    (j : OtherVertex i) :
    (parentRayToChildOption r i hir j).map
        (rayThetaAt
          (restrictedPoint_injective hp r)
          (survivingCentre r i hir))
      =
    parentAngleAfterDeleteOption hp r i j := by
  by_cases hjr : j.1 ≠ r
  · unfold parentRayToChildOption parentAngleAfterDeleteOption
    simp only [dif_pos hjr, Option.map_some]
    let b :=
      (childOtherEquivParentSurvivor r i hir).symm
        ⟨j, hjr⟩
    have hparent :
        childOtherToParent r i hir b = j := by
      have h :=
        (childOtherEquivParentSurvivor r i hir).apply_symm_apply
          ⟨j, hjr⟩
      exact congrArg Subtype.val h
    rw [rayThetaAt_restrict_delete hp r i hir b,
        hparent]
  · unfold parentRayToChildOption parentAngleAfterDeleteOption
    simp [hjr]

/-- Child angles are parent angles filtered by deletion of r. -/
theorem restrictDelete_angles_eq_filterMap_parent
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (r : V) (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir))) :
    (C.restrictDelete r hir hother).angles =
      C.rays.filterMap
        (parentAngleAfterDeleteOption hp r i) := by
  unfold CentreProjectiveCycle.angles
  rw [CentreProjectiveCycle.restrictDelete_rays]
  unfold restrictedRayList
  rw [List.map_filterMap]
  have hfun :
      (fun j =>
        (parentRayToChildOption r i hir j).map
          (rayThetaAt
            (restrictedPoint_injective hp r)
            (survivingCentre r i hir)))
        =
      parentAngleAfterDeleteOption hp r i := by
    funext j
    exact parentRayToChildOption_map_theta
      hp r i hir j
  rw [hfun]

/-- On a list containing no deleted ray, the theta filter is just map theta. -/
theorem filterMap_parentAngle_eq_map_of_all_ne
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (r i : V)
    (l : List (OtherVertex i))
    (hne : ∀ j ∈ l, j.1 ≠ r) :
    l.filterMap (parentAngleAfterDeleteOption hp r i) =
      l.map (rayThetaAt hp i) := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      have ha : a.1 ≠ r :=
        hne a (by simp)
      have htail :
          ∀ j ∈ l, j.1 ≠ r := by
        intro j hj
        exact hne j (by simp [hj])
      simp [parentAngleAfterDeleteOption, ha, ih htail]

/-- Every parent cycle contains the deleted ray and hence admits a split at
that exact ray. -/
theorem exists_parent_cycle_split_at_deleted
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (r : V) (hir : i ≠ r) :
    ∃ pre post,
      C.rays =
        pre ++ deletedParentRay r i hir :: post := by
  exact exists_append_cons_of_mem
    (C.mem_rays_iff (deletedParentRay r i hir))

/-- In a nodup split, no prefix or suffix ray can have deleted vertex r. -/
theorem parent_split_survivors_ne_deleted
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (r : V) (hir : i ≠ r)
    (pre post : List (OtherVertex i))
    (hsplit :
      C.rays =
        pre ++ deletedParentRay r i hir :: post) :
    (∀ j ∈ pre, j.1 ≠ r) ∧
    (∀ j ∈ post, j.1 ≠ r) := by
  have hnodup :
      (pre ++ deletedParentRay r i hir :: post).Nodup := by
    rw [← hsplit]
    exact C.nodup
  have hparts := List.nodup_append'.1 hnodup
  have hdisj := hparts.2.2
  have htailNodup := hparts.2.1
  have hdelNotPost :
      deletedParentRay r i hir ∉ post :=
    (List.nodup_cons.mp htailNodup).1
  constructor
  · intro j hj hjr
    have hjEq :
        j = deletedParentRay r i hir := by
      apply Subtype.ext
      simpa [deletedParentRay] using hjr
    have hright :
        deletedParentRay r i hir ∈
          deletedParentRay r i hir :: post := by simp
    exact List.disjoint_left.mp hdisj
      (by simpa [hjEq] using hj)
      hright
  · intro j hj hjr
    have hjEq :
        j = deletedParentRay r i hir := by
      apply Subtype.ext
      simpa [deletedParentRay] using hjr
    exact hdelNotPost (by simpa [hjEq] using hj)

/-- Main exact angle-list deletion formula. -/
theorem restrictDelete_angles_of_parent_split
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (r : V) (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    (pre post : List (OtherVertex i))
    (hsplit :
      C.rays =
        pre ++ deletedParentRay r i hir :: post) :
    (C.restrictDelete r hir hother).angles =
      pre.map (rayThetaAt hp i) ++
        post.map (rayThetaAt hp i) := by
  rw [restrictDelete_angles_eq_filterMap_parent]
  rw [hsplit, List.filterMap_append]
  have hne :=
    parent_split_survivors_ne_deleted
      C r hir pre post hsplit
  rw [filterMap_parentAngle_eq_map_of_all_ne
      hp r i pre hne.1]
  simp only [List.filterMap_cons]
  have hdel :
      ¬ (deletedParentRay r i hir).1 ≠ r := by
    simp [deletedParentRay]
  simp only [parentAngleAfterDeleteOption, hdel, dif_neg,
    List.filterMap_none]
  rw [filterMap_parentAngle_eq_map_of_all_ne
      hp r i post hne.2]

#print axioms restrictDelete_angles_eq_filterMap_parent
#print axioms exists_parent_cycle_split_at_deleted
#print axioms parent_split_survivors_ne_deleted
#print axioms restrictDelete_angles_of_parent_split

end JSP000404Research
