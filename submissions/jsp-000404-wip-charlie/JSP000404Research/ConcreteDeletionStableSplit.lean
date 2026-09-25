
import JSP000404Research.ConcreteCentreDeletionGain
import Mathlib.Tactic

/-!
# No unit gain forces a zero quotient beside the deleted ray

Fix a surviving centre i and delete another vertex r.  Split the sorted parent
ray list at the deleted ray

  rays = pre ++ deletedRay :: post.

The two projective gaps adjacent to deletedRay depend only on whether pre/post
are empty.

* first position: successor gap and cyclic wrap gap;
* interior position: predecessor gap and successor gap;
* last position: predecessor gap and cyclic wrap gap.

ConcreteCentreDeletionGain proves that positivity of both adjacent quotients
forces one full exponent unit of deletion gain.

This file packages the exact contrapositive uniformly over the three list
positions.  It is the concrete bridge from deletion stability to separated
positive cyclic quotient support.
-/

namespace JSP000404Research

open Real

def ParentSplitBothAdjacentPositive
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    (C : CentreProjectiveCycle hp i)
    (hir : i ≠ r)
    (pre post : List (OtherVertex i))
    (t : ℝ) : Prop :=
  let del := deletedParentRay r i hir
  match pre, post with
  | [], [] => False
  | [], b :: bs =>
      1 ≤ Nat.floor
        (t * ((rayThetaAt hp i b -
          rayThetaAt hp i del) / Real.pi))
      ∧
      1 ≤ Nat.floor
        (t * ((rayThetaAt hp i del + Real.pi -
          (bs.map (rayThetaAt hp i)).getLastD
            (rayThetaAt hp i b)) / Real.pi))
  | first :: mid, [] =>
      1 ≤ Nat.floor
        (t * ((rayThetaAt hp i del -
          (mid.map (rayThetaAt hp i)).getLastD
            (rayThetaAt hp i first)) / Real.pi))
      ∧
      1 ≤ Nat.floor
        (t * ((rayThetaAt hp i first + Real.pi -
          rayThetaAt hp i del) / Real.pi))
  | first :: mid, next :: tail =>
      1 ≤ Nat.floor
        (t * ((rayThetaAt hp i del -
          (mid.map (rayThetaAt hp i)).getLastD
            (rayThetaAt hp i first)) / Real.pi))
      ∧
      1 ≤ Nat.floor
        (t * ((rayThetaAt hp i next -
          rayThetaAt hp i del) / Real.pi))

/-- If deleting the split ray does not raise the centre exponent by one, its
two adjacent parent quotients cannot both be positive. -/
theorem not_bothAdjacentPositive_of_no_unit_gain
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
        pre ++ deletedParentRay r i hir :: post)
    {t : ℝ}
    (ht : 0 ≤ t)
    (hnoGain :
      ¬ centreExponent C t + 1 ≤
        centreExponent (C.restrictDelete r hir hother) t) :
    ¬ ParentSplitBothAdjacentPositive
        C hir pre post t := by
  intro hboth
  cases pre with
  | nil =>
      cases post with
      | nil =>
          simp [ParentSplitBothAdjacentPositive] at hboth
      | cons b bs =>
          have hsplit' :
              C.rays =
                deletedParentRay r i hir :: b :: bs := by
            simpa using hsplit
          have hgain :=
            centreExponent_gain_delete_first_ray
              C hir hother b bs hsplit' ht
              hboth.1 hboth.2
          exact hnoGain hgain
  | cons first mid =>
      cases post with
      | nil =>
          have hsplit' :
              C.rays =
                first :: (mid ++
                  [deletedParentRay r i hir]) := by
            simpa [List.append_assoc] using hsplit
          have hgain :=
            centreExponent_gain_delete_last_ray
              C hir hother first mid hsplit' ht
              hboth.1 hboth.2
          exact hnoGain hgain
      | cons next tail =>
          have hsplit' :
              C.rays =
                first :: (mid ++
                  deletedParentRay r i hir :: next :: tail) := by
            simpa [List.append_assoc] using hsplit
          have hgain :=
            centreExponent_gain_delete_interior_ray
              C hir hother first mid next tail
              hsplit' ht hboth.1 hboth.2
          exact hnoGain hgain

/-- Equivalent zero-quotient formulation, useful downstream. -/
theorem adjacent_zero_of_no_unit_gain
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
        pre ++ deletedParentRay r i hir :: post)
    {t : ℝ}
    (ht : 0 ≤ t)
    (hnoGain :
      ¬ centreExponent C t + 1 ≤
        centreExponent (C.restrictDelete r hir hother) t) :
    match pre, post with
    | [], [] => True
    | [], b :: bs =>
        Nat.floor
          (t * ((rayThetaAt hp i b -
            rayThetaAt hp i (deletedParentRay r i hir)) /
              Real.pi)) = 0
        ∨
        Nat.floor
          (t * ((rayThetaAt hp i (deletedParentRay r i hir) +
            Real.pi -
            (bs.map (rayThetaAt hp i)).getLastD
              (rayThetaAt hp i b)) / Real.pi)) = 0
    | first :: mid, [] =>
        Nat.floor
          (t * ((rayThetaAt hp i (deletedParentRay r i hir) -
            (mid.map (rayThetaAt hp i)).getLastD
              (rayThetaAt hp i first)) / Real.pi)) = 0
        ∨
        Nat.floor
          (t * ((rayThetaAt hp i first + Real.pi -
            rayThetaAt hp i (deletedParentRay r i hir)) /
              Real.pi)) = 0
    | first :: mid, next :: tail =>
        Nat.floor
          (t * ((rayThetaAt hp i (deletedParentRay r i hir) -
            (mid.map (rayThetaAt hp i)).getLastD
              (rayThetaAt hp i first)) / Real.pi)) = 0
        ∨
        Nat.floor
          (t * ((rayThetaAt hp i next -
            rayThetaAt hp i (deletedParentRay r i hir)) /
              Real.pi)) = 0 := by
  have hnot :=
    not_bothAdjacentPositive_of_no_unit_gain
      C hir hother pre post hsplit ht hnoGain
  cases pre with
  | nil =>
      cases post with
      | nil =>
          simp
      | cons b bs =>
          simp only [ParentSplitBothAdjacentPositive] at hnot
          push_neg at hnot
          by_cases hq :
              Nat.floor
                (t * ((rayThetaAt hp i b -
                  rayThetaAt hp i (deletedParentRay r i hir)) /
                    Real.pi)) = 0
          · exact Or.inl hq
          · right
            have hfirst :
                1 ≤ Nat.floor
                  (t * ((rayThetaAt hp i b -
                    rayThetaAt hp i (deletedParentRay r i hir)) /
                      Real.pi)) := by
              omega
            have hlast := hnot hfirst
            omega
  | cons first mid =>
      cases post with
      | nil =>
          simp only [ParentSplitBothAdjacentPositive] at hnot
          push_neg at hnot
          by_cases hq :
              Nat.floor
                (t * ((rayThetaAt hp i (deletedParentRay r i hir) -
                  (mid.map (rayThetaAt hp i)).getLastD
                    (rayThetaAt hp i first)) / Real.pi)) = 0
          · exact Or.inl hq
          · right
            have hleft :
                1 ≤ Nat.floor
                  (t * ((rayThetaAt hp i (deletedParentRay r i hir) -
                    (mid.map (rayThetaAt hp i)).getLastD
                      (rayThetaAt hp i first)) / Real.pi)) := by
              omega
            have hwrap := hnot hleft
            omega
      | cons next tail =>
          simp only [ParentSplitBothAdjacentPositive] at hnot
          push_neg at hnot
          by_cases hq :
              Nat.floor
                (t * ((rayThetaAt hp i (deletedParentRay r i hir) -
                  (mid.map (rayThetaAt hp i)).getLastD
                    (rayThetaAt hp i first)) / Real.pi)) = 0
          · exact Or.inl hq
          · right
            have hleft :
                1 ≤ Nat.floor
                  (t * ((rayThetaAt hp i (deletedParentRay r i hir) -
                    (mid.map (rayThetaAt hp i)).getLastD
                      (rayThetaAt hp i first)) / Real.pi)) := by
              omega
            have hright := hnot hleft
            omega

#print axioms not_bothAdjacentPositive_of_no_unit_gain
#print axioms adjacent_zero_of_no_unit_gain

end JSP000404Research
