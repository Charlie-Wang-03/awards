import JSP000404Research.CutValueDeletionGain
import JSP000404Research.CentreCycleRestrictionAngles
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# Exact cut-value list after deleting one ray

Let R be any centre ray cycle sorted at an arbitrary projective cut c, and
split its ray list at the ray to the deleted vertex:

  R.rays = pre ++ deletedRay :: post.

Let D be the actual restricted child centre cycle and Rc any child ray cycle
sorted at the same cut c.

The child normalized value list is exactly

  map cutValue pre ++ map cutValue post.

The proof deliberately does not assume unique projective theta values.
Instead:

* child rays are mapped canonically back to parent surviving rays;
* the mapped child list and pre++post are nodup and have identical membership,
  hence are permutations;
* cut coordinates are invariant under restriction;
* both real-value lists are sorted, so a permutation between them is equality.

This is the missing geometric adapter for CutValueDeletionGain.
-/

namespace JSP000404Research

/-- Two duplicate-free lists with the same membership are permutations. -/
theorem list_perm_of_nodup_mem_iff
    {α : Type*} [DecidableEq α]
    {xs ys : List α}
    (hx : xs.Nodup)
    (hy : ys.Nodup)
    (hmem : ∀ a, a ∈ xs ↔ a ∈ ys) :
    xs.Perm ys := by
  rw [List.perm_iff_count]
  intro a
  by_cases hax : a ∈ xs
  · have hay : a ∈ ys := (hmem a).1 hax
    rw [List.count_eq_one_of_mem hx hax,
        List.count_eq_one_of_mem hy hay]
  · have hay : a ∉ ys := by
      intro h
      exact hax ((hmem a).2 h)
    have hcx : xs.count a = 0 := by
      exact List.count_eq_zero.mpr hax
    have hcy : ys.count a = 0 := by
      exact List.count_eq_zero.mpr hay
    rw [hcx,hcy]

theorem childOtherToParent_injective
    {V : Type*}
    (r i : V) (hir : i ≠ r) :
    Function.Injective (childOtherToParent r i hir) := by
  intro a b hab
  apply (childOtherEquivParentSurvivor r i hir).injective
  apply Subtype.ext
  exact hab

theorem cutNormalizedRayTheta_restrict_delete
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (r i : V) (hir : i ≠ r)
    (t c : ℝ)
    (j : OtherVertex (survivingCentre r i hir)) :
    cutNormalizedRayTheta
        (restrictedPoint_injective hp r)
        t c (survivingCentre r i hir) j
      =
    cutNormalizedRayTheta hp t c i
      (childOtherToParent r i hir j) := by
  unfold cutNormalizedRayTheta cutRayTheta
  rw [rayThetaAt_restrict_delete hp r i hir j]

/-- The mapped child cut-ray list contains exactly the parent rays different
from the deleted vertex. -/
theorem mem_map_childOtherToParent_iff_ne_deleted
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    {C : CentreProjectiveCycle hp i}
    {c : ℝ}
    (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    (D := C.restrictDelete r hir hother)
    (Rc :
      CentreCutRayCycle
        (restrictedPoint_injective hp r) D c)
    (j : OtherVertex i) :
    j ∈ Rc.rays.map (childOtherToParent r i hir)
      ↔
    j.1 ≠ r := by
  constructor
  · intro hj
    obtain ⟨x,_hx,hxj⟩ := List.mem_map.mp hj
    rw [← hxj]
    exact childOtherToParent_ne_deleted r i hir x
  · intro hjr
    let x : OtherVertex (survivingCentre r i hir) :=
      (childOtherEquivParentSurvivor r i hir).symm
        ⟨j,hjr⟩
    have hxmem : x ∈ Rc.rays :=
      Rc.mem_rays x
    refine List.mem_map.mpr ⟨x,hxmem,?_⟩
    have hback :=
      (childOtherEquivParentSurvivor r i hir).apply_symm_apply
        ⟨j,hjr⟩
    exact congrArg Subtype.val hback

/-- Parent prefix/suffix after splitting at the deleted ray contain exactly
the surviving parent rays. -/
theorem mem_parent_cut_split_without_deleted_iff
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    {C : CentreProjectiveCycle hp i}
    {c : ℝ}
    (R : CentreCutRayCycle hp C c)
    (hir : i ≠ r)
    (pre post : List (OtherVertex i))
    (hsplit :
      R.rays =
        pre ++ deletedParentRay r i hir :: post)
    (j : OtherVertex i) :
    j ∈ pre ++ post ↔ j.1 ≠ r := by
  have hnod :
      (pre ++ deletedParentRay r i hir :: post).Nodup := by
    rw [← hsplit]
    exact R.nodup
  have hmid :
      (deletedParentRay r i hir :: (pre ++ post)).Nodup :=
    (List.nodup_middle.mp hnod)
  have hdelNot :
      deletedParentRay r i hir ∉ pre ++ post :=
    (List.nodup_cons.mp hmid).1
  constructor
  · intro hj hjr
    have hjeq :
        j = deletedParentRay r i hir := by
      apply Subtype.ext
      simpa [deletedParentRay] using hjr
    exact hdelNot (by simpa [hjeq] using hj)
  · intro hjr
    have hjAll : j ∈ R.rays :=
      R.mem_rays j
    rw [hsplit, List.mem_append, List.mem_cons] at hjAll
    rcases hjAll with hpre | hdel | hpost
    · exact List.mem_append.mpr (Or.inl hpre)
    · have : j.1 = r := by
        rw [hdel]
        rfl
      exact False.elim (hjr this)
    · exact List.mem_append.mpr (Or.inr hpost)

/-- The child rays, mapped back to parent rays, are a permutation of the
parent cut list with the deleted ray removed. -/
theorem child_parent_ray_list_perm_split
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    {C : CentreProjectiveCycle hp i}
    {c : ℝ}
    (R : CentreCutRayCycle hp C c)
    (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    (D := C.restrictDelete r hir hother)
    (Rc :
      CentreCutRayCycle
        (restrictedPoint_injective hp r) D c)
    (pre post : List (OtherVertex i))
    (hsplit :
      R.rays =
        pre ++ deletedParentRay r i hir :: post) :
    Rc.rays.map (childOtherToParent r i hir)
      ~
    pre ++ post := by
  have hleft :
      (Rc.rays.map (childOtherToParent r i hir)).Nodup :=
    Rc.nodup.map
      (childOtherToParent_injective r i hir)
  have hfull :
      (pre ++ deletedParentRay r i hir :: post).Nodup := by
    rw [← hsplit]
    exact R.nodup
  have hright :
      (pre ++ post).Nodup := by
    have hmid :
        (deletedParentRay r i hir :: (pre ++ post)).Nodup :=
      List.nodup_middle.mp hfull
    exact (List.nodup_cons.mp hmid).2
  apply list_perm_of_nodup_mem_iff hleft hright
  intro j
  rw [mem_map_childOtherToParent_iff_ne_deleted
      hir hother Rc j,
    mem_parent_cut_split_without_deleted_iff
      R hir pre post hsplit j]

/-- Removing one ray from a cut-sorted parent list preserves cutTheta order. -/
theorem parent_cut_split_without_deleted_sorted
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    {C : CentreProjectiveCycle hp i}
    {c : ℝ}
    (R : CentreCutRayCycle hp C c)
    (hir : i ≠ r)
    (pre post : List (OtherVertex i))
    (hsplit :
      R.rays =
        pre ++ deletedParentRay r i hir :: post) :
    (pre ++ post).Pairwise
      (fun a b =>
        cutRayTheta hp c i a ≤ cutRayTheta hp c i b) := by
  have hfull :
      (pre ++ deletedParentRay r i hir :: post).Pairwise
        (fun a b =>
          cutRayTheta hp c i a ≤ cutRayTheta hp c i b) := by
    rw [← hsplit]
    exact R.cutTheta_sorted
  have hparts :
      pre.Pairwise
          (fun a b =>
            cutRayTheta hp c i a ≤ cutRayTheta hp c i b)
      ∧
      (deletedParentRay r i hir :: post).Pairwise
          (fun a b =>
            cutRayTheta hp c i a ≤ cutRayTheta hp c i b)
      ∧
      (∀ a ∈ pre,
        ∀ b ∈ deletedParentRay r i hir :: post,
          cutRayTheta hp c i a ≤ cutRayTheta hp c i b) := by
    simpa only [List.pairwise_append] using hfull
  apply List.pairwise_append.mpr
  refine ⟨hparts.1, (List.pairwise_cons.mp hparts.2.1).2, ?_⟩
  intro a ha b hb
  exact hparts.2.2 a ha b (by simp [hb])

/-- Exact cut-normalized child value list after deleting one displayed parent
ray. -/
theorem restrictDelete_normalizedValues_of_cut_split
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    {C : CentreProjectiveCycle hp i}
    {c t : ℝ}
    (R : CentreCutRayCycle hp C c)
    (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    (D := C.restrictDelete r hir hother)
    (Rc :
      CentreCutRayCycle
        (restrictedPoint_injective hp r) D c)
    (ht : 0 < t)
    (pre post : List (OtherVertex i))
    (hsplit :
      R.rays =
        pre ++ deletedParentRay r i hir :: post) :
    Rc.normalizedValues t =
      (pre ++ post).map
        (cutNormalizedRayTheta hp t c i) := by
  have hpermRays :=
    child_parent_ray_list_perm_split
      R hir hother Rc pre post hsplit
  have hpermValues :
      Rc.normalizedValues t
        ~
      (pre ++ post).map
        (cutNormalizedRayTheta hp t c i) := by
    have hmap :
        Rc.normalizedValues t =
          (Rc.rays.map (childOtherToParent r i hir)).map
            (cutNormalizedRayTheta hp t c i) := by
      unfold CentreCutRayCycle.normalizedValues
      rw [List.map_map]
      apply List.map_congr_left
      intro j hj
      exact cutNormalizedRayTheta_restrict_delete
        hp r i hir t c j
    rw [hmap]
    exact hpermRays.map
      (cutNormalizedRayTheta hp t c i)

  have hleft :
      (Rc.normalizedValues t).Pairwise (· ≤ ·) :=
    Rc.normalizedValues_pairwise ht.le

  have hrightTheta :=
    parent_cut_split_without_deleted_sorted
      R hir pre post hsplit
  have hright :
      ((pre ++ post).map
        (cutNormalizedRayTheta hp t c i)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    intro a ha b hb hab
    unfold cutNormalizedRayTheta
    have hdiv :=
      div_le_div_of_nonneg_right hab Real.pi_pos.le
    exact mul_le_mul_of_nonneg_left hdiv ht.le

  exact List.Perm.eq_of_pairwise
    (fun a b _ha _hb hab hba => le_antisymm hab hba)
    hleft hright hpermValues

#print axioms list_perm_of_nodup_mem_iff
#print axioms cutNormalizedRayTheta_restrict_delete
#print axioms child_parent_ray_list_perm_split
#print axioms restrictDelete_normalizedValues_of_cut_split

end JSP000404Research
