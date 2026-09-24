import JSP000404Research.CentreCycleRestrictionAngles
import JSP000404Research.GeneralProjectiveGapDeletion
import JSP000404Research.MiddleProjectiveGapDeletion
import JSP000404Research.LastProjectiveGapDeletion
import JSP000404Research.CentreExponent
import Mathlib.Tactic

/-!
# Concrete centre exponent gain under deletion

The list-level first/interior/last deletion lemmas are now lifted to actual
CentreProjectiveCycle objects.

Fix a surviving centre i and delete another vertex r.  Construct the child
cycle by filtering the ray i--r from the parent cycle.  In each of the three
possible positions of that deleted ray in the sorted parent list, if the two
cyclic parent quotient gaps adjacent to i--r are positive, then the child
centre exponent rises by at least one.

These are the concrete local gain theorems needed by compensated-deletion
induction.
-/

namespace JSP000404Research

open Real

/-- First-position deletion. -/
theorem centreExponent_gain_delete_first_ray
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    (C : CentreProjectiveCycle hp i)
    (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    (b : OtherVertex i)
    (bs : List (OtherVertex i))
    (hrays :
      C.rays =
        deletedParentRay r i hir :: b :: bs)
    {t : ℝ}
    (ht : 0 ≤ t)
    (hFirst :
      1 ≤ Nat.floor
        (t * ((rayThetaAt hp i b -
          rayThetaAt hp i (deletedParentRay r i hir)) /
            Real.pi)))
    (hLast :
      1 ≤ Nat.floor
        (t * ((rayThetaAt hp i (deletedParentRay r i hir) +
          Real.pi -
          (bs.map (rayThetaAt hp i)).getLastD
            (rayThetaAt hp i b)) / Real.pi))) :
    centreExponent C t + 1 ≤
      centreExponent
        (C.restrictDelete r hir hother) t := by
  let del := deletedParentRay r i hir
  let child := C.restrictDelete r hir hother
  have hParentAngles :
      C.angles =
        rayThetaAt hp i del ::
          rayThetaAt hp i b ::
            bs.map (rayThetaAt hp i) := by
    simp [CentreProjectiveCycle.angles, hrays, del]
  have hsplit :
      C.rays = [] ++ del :: (b :: bs) := by
    simpa [del] using hrays
  have hChildAngles :
      child.angles =
        rayThetaAt hp i b ::
          bs.map (rayThetaAt hp i) := by
    dsimp [child]
    simpa [del] using
      (restrictDelete_angles_of_parent_split
        C r hir hother [] (b :: bs) hsplit)
  have horder :
      rayThetaAt hp i del ≤
        rayThetaAt hp i b := by
    have hs := C.theta_sorted
    rw [hrays] at hs
    rw [List.pairwise_cons] at hs
    exact hs.1 b (by simp)
  have hdel0 :
      0 ≤ rayThetaAt hp i del :=
    rayThetaAt_nonneg hp i del
  have hall :
      ∀ theta ∈
          rayThetaAt hp i b ::
            bs.map (rayThetaAt hp i),
        theta < Real.pi := by
    intro theta htheta
    simp only [List.mem_cons, List.mem_map] at htheta
    rcases htheta with rfl | ⟨j, _hj, rfl⟩
    · exact rayThetaAt_lt_pi hp i b
    · exact rayThetaAt_lt_pi hp i j
  have hlastPi :
      (bs.map (rayThetaAt hp i)).getLastD
          (rayThetaAt hp i b) < Real.pi :=
    getLastD_lt_pi_of_all_lt
      (rayThetaAt hp i b)
      (bs.map (rayThetaAt hp i))
      hall
  rw [← listExponent_quotientList_eq_centreExponent' C t,
      ← listExponent_quotientList_eq_centreExponent' child t]
  unfold CentreProjectiveCycle.gaps
  rw [hParentAngles, hChildAngles]
  exact listExponent_delete_first_general_gain
    ht horder hdel0 hlastPi
    (by simpa [del] using hFirst)
    (by simpa [del] using hLast)

/-- Interior-position deletion. -/
theorem centreExponent_gain_delete_interior_ray
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    (C : CentreProjectiveCycle hp i)
    (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    (first : OtherVertex i)
    (pre : List (OtherVertex i))
    (next : OtherVertex i)
    (tail : List (OtherVertex i))
    (hrays :
      C.rays =
        first :: (pre ++
          deletedParentRay r i hir :: next :: tail))
    {t : ℝ}
    (ht : 0 ≤ t)
    (hLeft :
      1 ≤ Nat.floor
        (t * ((rayThetaAt hp i
              (deletedParentRay r i hir) -
            (pre.map (rayThetaAt hp i)).getLastD
              (rayThetaAt hp i first)) / Real.pi)))
    (hRight :
      1 ≤ Nat.floor
        (t * ((rayThetaAt hp i next -
          rayThetaAt hp i
            (deletedParentRay r i hir)) / Real.pi))) :
    centreExponent C t + 1 ≤
      centreExponent
        (C.restrictDelete r hir hother) t := by
  let del := deletedParentRay r i hir
  let child := C.restrictDelete r hir hother
  let preAngles := pre.map (rayThetaAt hp i)
  let tailAngles := tail.map (rayThetaAt hp i)
  let a := rayThetaAt hp i first
  let x := rayThetaAt hp i del
  let y := rayThetaAt hp i next
  have hParentAngles :
      C.angles =
        a :: (preAngles ++ x :: y :: tailAngles) := by
    simp [CentreProjectiveCycle.angles, hrays,
      a, x, y, preAngles, tailAngles, del]
  have hsplit :
      C.rays =
        (first :: pre) ++ del :: (next :: tail) := by
    simpa [List.append_assoc, del] using hrays
  have hChildAngles :
      child.angles =
        a :: (preAngles ++ y :: tailAngles) := by
    dsimp [child]
    have h :=
      restrictDelete_angles_of_parent_split
        C r hir hother
        (first :: pre) (next :: tail) hsplit
    simpa [a, y, preAngles, tailAngles, del,
      List.map_append, List.append_assoc] using h
  have hParentGaps :
      C.gaps =
        normalizedPrefixGaps a preAngles ++
          [(x - preAngles.getLastD a) / Real.pi,
           (y - x) / Real.pi] ++
          normalizedSuffixGaps y tailAngles ++
          [(a + Real.pi -
            tailAngles.getLastD y) / Real.pi] := by
    unfold CentreProjectiveCycle.gaps
    rw [hParentAngles,
        normalizedProjectiveGaps_interior_parent]
  have hgLeft :
      0 ≤ (x - preAngles.getLastD a) / Real.pi := by
    exact C.gaps_nonneg _
      (by rw [hParentGaps]; simp)
  have hgRight :
      0 ≤ (y - x) / Real.pi := by
    exact C.gaps_nonneg _
      (by rw [hParentGaps]; simp)
  rw [← listExponent_quotientList_eq_centreExponent' C t,
      ← listExponent_quotientList_eq_centreExponent' child t]
  unfold CentreProjectiveCycle.gaps
  rw [hParentAngles, hChildAngles]
  exact listExponent_gain_delete_interior
    ht hgLeft hgRight
    (by simpa [x, preAngles, a, del] using hLeft)
    (by simpa [x, y, del] using hRight)

/-- Last-position deletion. -/
theorem centreExponent_gain_delete_last_ray
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    (C : CentreProjectiveCycle hp i)
    (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    (first : OtherVertex i)
    (pre : List (OtherVertex i))
    (hrays :
      C.rays =
        first :: (pre ++
          [deletedParentRay r i hir]))
    {t : ℝ}
    (ht : 0 ≤ t)
    (hLeft :
      1 ≤ Nat.floor
        (t * ((rayThetaAt hp i
              (deletedParentRay r i hir) -
            (pre.map (rayThetaAt hp i)).getLastD
              (rayThetaAt hp i first)) / Real.pi)))
    (hWrap :
      1 ≤ Nat.floor
        (t * ((rayThetaAt hp i first + Real.pi -
          rayThetaAt hp i
            (deletedParentRay r i hir)) / Real.pi))) :
    centreExponent C t + 1 ≤
      centreExponent
        (C.restrictDelete r hir hother) t := by
  let del := deletedParentRay r i hir
  let child := C.restrictDelete r hir hother
  let preAngles := pre.map (rayThetaAt hp i)
  let a := rayThetaAt hp i first
  let x := rayThetaAt hp i del
  have hParentAngles :
      C.angles =
        a :: (preAngles ++ [x]) := by
    simp [CentreProjectiveCycle.angles, hrays,
      a, x, preAngles, del]
  have hsplit :
      C.rays =
        (first :: pre) ++ del :: [] := by
    simpa [List.append_assoc, del] using hrays
  have hChildAngles :
      child.angles =
        a :: preAngles := by
    dsimp [child]
    have h :=
      restrictDelete_angles_of_parent_split
        C r hir hother
        (first :: pre) [] hsplit
    simpa [a, preAngles, del,
      List.map_append, List.append_assoc] using h
  have hParentGaps :
      C.gaps =
        normalizedPrefixGaps a preAngles ++
          [(x - preAngles.getLastD a) / Real.pi,
           (a + Real.pi - x) / Real.pi] := by
    unfold CentreProjectiveCycle.gaps
    rw [hParentAngles,
        normalizedProjectiveGaps_last_parent]
  have hgLeft :
      0 ≤ (x - preAngles.getLastD a) / Real.pi := by
    exact C.gaps_nonneg _
      (by rw [hParentGaps]; simp)
  have hgWrap :
      0 ≤ (a + Real.pi - x) / Real.pi := by
    exact C.gaps_nonneg _
      (by rw [hParentGaps]; simp)
  rw [← listExponent_quotientList_eq_centreExponent' C t,
      ← listExponent_quotientList_eq_centreExponent' child t]
  unfold CentreProjectiveCycle.gaps
  rw [hParentAngles, hChildAngles]
  exact listExponent_gain_delete_last
    ht hgLeft hgWrap
    (by simpa [x, preAngles, a, del] using hLeft)
    (by simpa [x, a, del] using hWrap)

#print axioms centreExponent_gain_delete_first_ray
#print axioms centreExponent_gain_delete_interior_ray
#print axioms centreExponent_gain_delete_last_ray

end JSP000404Research
