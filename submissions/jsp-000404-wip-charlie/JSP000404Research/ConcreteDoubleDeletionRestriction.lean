import JSP000404Research.CentreCycleRestrictionAngles
import JSP000404Research.ConcreteSecondDeletionRigidity
import Mathlib.Tactic

/-!
# Exact ray/angle lists after two adjacent concrete deletions

Suppose that at a surviving centre i the parent projective ray list contains
two adjacent rays to r and s:

  rays = pre ++ ray(r) :: ray(s) :: post.

Deleting r preserves the order of every surviving ray, so the ray to s remains
at the same cut in the child.  Deleting that child ray next therefore removes
exactly the two adjacent parent rays.

This file makes that subtype transport explicit.  Its main consequence is the
exact grandchild angle-list identity

  grandchild.angles = map theta pre ++ map theta post.

No exponent or extremal assumption is used here.
-/

namespace JSP000404Research

/-- The child ray corresponding to a specified surviving parent ray. -/
noncomputable def parentSurvivorRayToChild
    {V : Type*}
    (r i : V) (hir : i ≠ r)
    (j : OtherVertex i) (hjr : j.1 ≠ r) :
    OtherVertex (survivingCentre r i hir) :=
  (childOtherEquivParentSurvivor r i hir).symm
    ⟨j, hjr⟩

@[simp] theorem parentRayToChildOption_eq_some_parentSurvivorRayToChild
    {V : Type*}
    (r i : V) (hir : i ≠ r)
    (j : OtherVertex i) (hjr : j.1 ≠ r) :
    parentRayToChildOption r i hir j =
      some (parentSurvivorRayToChild r i hir j hjr) := by
  simp [parentRayToChildOption, parentSurvivorRayToChild, hjr]

@[simp] theorem parentRayToChildOption_deletedParentRay
    {V : Type*}
    (r i : V) (hir : i ≠ r) :
    parentRayToChildOption r i hir
        (deletedParentRay r i hir)
      =
    none := by
  unfold parentRayToChildOption
  simp [deletedParentRay]

/-- Exact ray-list deletion formula, retaining the child subtype transport. -/
theorem restrictDelete_rays_of_parent_split_filterMap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    (C : CentreProjectiveCycle hp i)
    (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    (pre post : List (OtherVertex i))
    (hsplit :
      C.rays =
        pre ++ deletedParentRay r i hir :: post) :
    (C.restrictDelete r hir hother).rays =
      pre.filterMap (parentRayToChildOption r i hir) ++
        post.filterMap (parentRayToChildOption r i hir) := by
  rw [CentreProjectiveCycle.restrictDelete_rays]
  unfold restrictedRayList
  rw [hsplit, List.filterMap_append]
  simp

/-- Mapping child theta over a transported survivor segment recovers the
original parent theta segment. -/
theorem map_filterMap_parentSurvivors_theta
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (r i : V) (hir : i ≠ r)
    (l : List (OtherVertex i))
    (hne : ∀ j ∈ l, j.1 ≠ r) :
    (l.filterMap (parentRayToChildOption r i hir)).map
        (rayThetaAt
          (restrictedPoint_injective hp r)
          (survivingCentre r i hir))
      =
    l.map (rayThetaAt hp i) := by
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
  exact filterMap_parentAngle_eq_map_of_all_ne
    hp r i l hne

/-- In the first child, the transported parent ray to s is exactly the
canonical deletedParentRay for the second deletion. -/
theorem parentSurvivorRayToChild_deletedParentRay_eq
    {V : Type*}
    (r s i : V)
    (hir : i ≠ r)
    (his : i ≠ s)
    (hsr : s ≠ r)
    (hiChild :
      survivingCentre r i hir ≠ childVertex r s hsr) :
    parentSurvivorRayToChild r i hir
        (deletedParentRay s i his) hsr
      =
    deletedParentRay
      (childVertex r s hsr)
      (survivingCentre r i hir)
      hiChild := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Adjacent parent rays stay adjacent after the first deletion: the s-ray is
the exact second-deletion ray in the child list. -/
theorem restrictDelete_rays_adjacent_second_cut
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r s : V}
    (C : CentreProjectiveCycle hp i)
    (hir : i ≠ r)
    (his : i ≠ s)
    (hrs : r ≠ s)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    (pre post : List (OtherVertex i))
    (hsplit :
      C.rays =
        pre ++
          deletedParentRay r i hir ::
          deletedParentRay s i his ::
          post) :
    let sChild : DeletedVertexType r :=
      childVertex r s hrs.symm
    let iChild : DeletedVertexType r :=
      survivingCentre r i hir
    let hiChild : iChild ≠ sChild := by
      intro h
      apply his
      exact congrArg Subtype.val h
    (C.restrictDelete r hir hother).rays =
      pre.filterMap (parentRayToChildOption r i hir) ++
        deletedParentRay sChild iChild hiChild ::
          post.filterMap (parentRayToChildOption r i hir) := by
  dsimp
  let sChild : DeletedVertexType r :=
    childVertex r s hrs.symm
  let iChild : DeletedVertexType r :=
    survivingCentre r i hir
  have hiChild : iChild ≠ sChild := by
    intro h
    apply his
    exact congrArg Subtype.val h
  have hfirst :=
    restrictDelete_rays_of_parent_split_filterMap
      C hir hother pre
      (deletedParentRay s i his :: post)
      hsplit
  rw [hfirst]
  simp only [List.filterMap_cons]
  have hsSome :
      parentRayToChildOption r i hir
          (deletedParentRay s i his)
        =
      some
        (parentSurvivorRayToChild r i hir
          (deletedParentRay s i his) hrs.symm) := by
    exact
      parentRayToChildOption_eq_some_parentSurvivorRayToChild
        r i hir (deletedParentRay s i his) hrs.symm
  rw [hsSome]
  simp only [List.filterMap_some]
  have hRayEq :
      parentSurvivorRayToChild r i hir
          (deletedParentRay s i his) hrs.symm
        =
      deletedParentRay sChild iChild hiChild := by
    exact parentSurvivorRayToChild_deletedParentRay_eq
      r s i hir his hrs.symm hiChild
  rw [hRayEq]

/-- Exact angle list after deleting two adjacent parent rays r then s. -/
theorem restrictDelete_twice_angles_of_adjacent_parent_split
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {i r s : V}
    (C : CentreProjectiveCycle hp i)
    (hir : i ≠ r)
    (his : i ≠ s)
    (hrs : r ≠ s)
    (hotherR :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    (pre post : List (OtherVertex i))
    (hsplit :
      C.rays =
        pre ++
          deletedParentRay r i hir ::
          deletedParentRay s i his ::
          post)
    (hotherS :
      let sChild : DeletedVertexType r :=
        childVertex r s hrs.symm
      let iChild : DeletedVertexType r :=
        survivingCentre r i hir
      let hiChild : iChild ≠ sChild := by
        intro h
        apply his
        exact congrArg Subtype.val h
      Nonempty
        (OtherVertex
          (survivingCentre sChild iChild hiChild))) :
    let sChild : DeletedVertexType r :=
      childVertex r s hrs.symm
    let iChild : DeletedVertexType r :=
      survivingCentre r i hir
    let hiChild : iChild ≠ sChild := by
      intro h
      apply his
      exact congrArg Subtype.val h
    let child :=
      C.restrictDelete r hir hotherR
    (child.restrictDelete sChild hiChild hotherS).angles =
      pre.map (rayThetaAt hp i) ++
        post.map (rayThetaAt hp i) := by
  dsimp
  let sChild : DeletedVertexType r :=
    childVertex r s hrs.symm
  let iChild : DeletedVertexType r :=
    survivingCentre r i hir
  have hiChild : iChild ≠ sChild := by
    intro h
    apply his
    exact congrArg Subtype.val h
  let child :=
    C.restrictDelete r hir hotherR
  let preChild :=
    pre.filterMap (parentRayToChildOption r i hir)
  let postChild :=
    post.filterMap (parentRayToChildOption r i hir)
  have hchildSplit :
      child.rays =
        preChild ++
          deletedParentRay sChild iChild hiChild ::
          postChild := by
    dsimp [child, preChild, postChild]
    exact restrictDelete_rays_adjacent_second_cut
      C hir his hrs hotherR pre post hsplit
  have hAngles :=
    restrictDelete_angles_of_parent_split
      child sChild hiChild hotherS
      preChild postChild hchildSplit
  have hsurv :=
    parent_split_survivors_ne_deleted
      C r hir pre
      (deletedParentRay s i his :: post)
      hsplit
  have hpreNe : ∀ j ∈ pre, j.1 ≠ r :=
    hsurv.1
  have hpostNe : ∀ j ∈ post, j.1 ≠ r := by
    intro j hj
    exact hsurv.2 j (by simp [hj])
  have hpreTheta :
      preChild.map
          (rayThetaAt
            (restrictedPoint_injective hp r) iChild)
        =
      pre.map (rayThetaAt hp i) := by
    dsimp [preChild, iChild]
    exact map_filterMap_parentSurvivors_theta
      hp r i hir pre hpreNe
  have hpostTheta :
      postChild.map
          (rayThetaAt
            (restrictedPoint_injective hp r) iChild)
        =
      post.map (rayThetaAt hp i) := by
    dsimp [postChild, iChild]
    exact map_filterMap_parentSurvivors_theta
      hp r i hir post hpostNe
  rw [hAngles, hpreTheta, hpostTheta]

#print axioms restrictDelete_rays_of_parent_split_filterMap
#print axioms map_filterMap_parentSurvivors_theta
#print axioms restrictDelete_rays_adjacent_second_cut
#print axioms restrictDelete_twice_angles_of_adjacent_parent_split

end JSP000404Research
