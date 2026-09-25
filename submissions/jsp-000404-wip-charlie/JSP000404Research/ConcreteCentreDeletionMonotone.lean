
import JSP000404Research.ConcreteCentreDeletionGain
import Mathlib.Tactic

/-!
# Concrete centre exponent monotonicity under deletion

Deleting another vertex merges exactly two adjacent quotient gaps at every
surviving centre.  MergeGain proves that such a merge can never decrease the
Sendov excess contribution.

ConcreteCentreDeletionGain already supplies all geometric/list decompositions
for the first, interior, and last possible position of the deleted ray.  Here
we reuse those decompositions without positivity hypotheses and obtain the
global monotonicity statement needed by compensated-deletion induction.
-/

namespace JSP000404Research

open Real

/-- List-level displayed merge monotonicity. -/
theorem listExponent_merge_mono
    (pre post : List ℕ) (a b carry : ℕ) :
    listExponent (pre ++ a :: b :: post) ≤
      listExponent
        (mergeDisplayedAdjacent pre a b carry post) := by
  rw [listExponent_displayed_pair,
      listExponent_merged_displayed_pair]
  have h := excess_merge_mono a b carry
  omega

/-- Pinned cyclic merge monotonicity. -/
theorem pinned_cyclic_merge_mono
    (qFirst qLast carry : ℕ)
    (qmid : List ℕ) :
    listExponent (qFirst :: qmid ++ [qLast]) ≤
      listExponent (qmid ++ [qLast + qFirst + carry]) := by
  rw [listExponent_pinned, listExponent_pinned_child]
  have h := excess_merge_mono qLast qFirst carry
  omega

/-- First-position list deletion is monotone. -/
theorem listExponent_delete_first_general_mono
    {t a b : ℝ} {bs : List ℝ}
    (ht : 0 ≤ t)
    (hab : a ≤ b)
    (ha0 : 0 ≤ a)
    (hlastPi : bs.getLastD b < Real.pi) :
    listExponent
        (quotientList t
          (normalizedProjectiveGaps (a :: b :: bs)))
      ≤
    listExponent
        (quotientList t
          (normalizedProjectiveGaps (b :: bs))) := by
  obtain ⟨carry, _hcarry, hchild⟩ :=
    quotientList_delete_first_general
      ht hab ha0 hlastPi
  rw [quotientList_cons_cons_parent, hchild]
  exact pinned_cyclic_merge_mono
    (Nat.floor (t * firstNormalizedGap a b))
    (Nat.floor (t * lastNormalizedGap a b bs))
    carry
    (quotientList t (normalizedSuccessiveTail b bs))

/-- Interior-position list deletion is monotone. -/
theorem listExponent_delete_interior_mono
    {t a x y : ℝ}
    {pre tail : List ℝ}
    (ht : 0 ≤ t)
    (hgLeft :
      0 ≤ (x - pre.getLastD a) / Real.pi)
    (hgRight :
      0 ≤ (y - x) / Real.pi) :
    listExponent
        (quotientList t
          (normalizedProjectiveGaps
            (a :: (pre ++ x :: y :: tail))))
      ≤
    listExponent
        (quotientList t
          (normalizedProjectiveGaps
            (a :: (pre ++ y :: tail)))) := by
  obtain ⟨carry, _hcarry, hparent, hchild⟩ :=
    quotientList_delete_interior
      ht hgLeft hgRight
  let prefix :=
    quotientList t (normalizedPrefixGaps a pre)
  let suffix :=
    quotientList t (normalizedSuffixGaps y tail) ++
      [Nat.floor
        (t * ((a + Real.pi - tail.getLastD y) / Real.pi))]
  let qLeft :=
    Nat.floor
      (t * ((x - pre.getLastD a) / Real.pi))
  let qRight :=
    Nat.floor
      (t * ((y - x) / Real.pi))
  have hp :
      quotientList t
          (normalizedProjectiveGaps
            (a :: (pre ++ x :: y :: tail)))
        =
      prefix ++ qLeft :: qRight :: suffix := by
    simpa [prefix, suffix, qLeft, qRight,
      List.append_assoc] using hparent
  have hc :
      quotientList t
          (normalizedProjectiveGaps
            (a :: (pre ++ y :: tail)))
        =
      mergeDisplayedAdjacent
        prefix qLeft qRight carry suffix := by
    simpa [prefix, suffix, qLeft, qRight,
      mergeDisplayedAdjacent, List.append_assoc]
      using hchild
  rw [hp, hc]
  exact listExponent_merge_mono
    prefix suffix qLeft qRight carry

/-- Last-position list deletion is monotone. -/
theorem listExponent_delete_last_mono
    {t a x : ℝ} {pre : List ℝ}
    (ht : 0 ≤ t)
    (hgLeft :
      0 ≤ (x - pre.getLastD a) / Real.pi)
    (hgWrap :
      0 ≤ (a + Real.pi - x) / Real.pi) :
    listExponent
        (quotientList t
          (normalizedProjectiveGaps
            (a :: (pre ++ [x]))))
      ≤
    listExponent
        (quotientList t
          (normalizedProjectiveGaps (a :: pre))) := by
  obtain ⟨carry, _hcarry, hparent, hchild⟩ :=
    quotientList_delete_last
      ht hgLeft hgWrap
  let prefix :=
    quotientList t (normalizedPrefixGaps a pre)
  let qLeft :=
    Nat.floor
      (t * ((x - pre.getLastD a) / Real.pi))
  let qWrap :=
    Nat.floor
      (t * ((a + Real.pi - x) / Real.pi))
  have hp :
      quotientList t
          (normalizedProjectiveGaps
            (a :: (pre ++ [x])))
        =
      prefix ++ qLeft :: qWrap :: [] := by
    simpa [prefix, qLeft, qWrap,
      List.append_assoc] using hparent
  have hc :
      quotientList t
          (normalizedProjectiveGaps (a :: pre))
        =
      mergeDisplayedAdjacent
        prefix qLeft qWrap carry [] := by
    simpa [prefix, qLeft, qWrap,
      mergeDisplayedAdjacent, List.append_assoc]
      using hchild
  rw [hp, hc]
  exact listExponent_merge_mono
    prefix [] qLeft qWrap carry

/-- First-position concrete deletion never decreases the survivor exponent. -/
theorem centreExponent_mono_delete_first_ray
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
    (ht : 0 ≤ t) :
    centreExponent C t ≤
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
  exact listExponent_delete_first_general_mono
    ht horder hdel0 hlastPi

/-- Interior-position concrete deletion never decreases the survivor exponent. -/
theorem centreExponent_mono_delete_interior_ray
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
    (ht : 0 ≤ t) :
    centreExponent C t ≤
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
  exact listExponent_delete_interior_mono
    ht hgLeft hgRight

/-- Last-position concrete deletion never decreases the survivor exponent. -/
theorem centreExponent_mono_delete_last_ray
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
    (ht : 0 ≤ t) :
    centreExponent C t ≤
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
  exact listExponent_delete_last_mono
    ht hgLeft hgWrap


/-- Unified concrete monotonicity for deletion of an arbitrary other vertex. -/
theorem centreExponent_mono_restrictDelete
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    (C : CentreProjectiveCycle hp i)
    (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    {t : ℝ}
    (ht : 0 ≤ t) :
    centreExponent C t ≤
      centreExponent
        (C.restrictDelete r hir hother) t := by
  obtain ⟨pre, post, hsplit⟩ :=
    exists_parent_cycle_split_at_deleted C r hir
  cases pre with
  | nil =>
      cases post with
      | nil =>
          let child := C.restrictDelete r hir hother
          have hchildAngles :
              child.angles = [] := by
            dsimp [child]
            simpa using
              (restrictDelete_angles_of_parent_split
                C r hir hother [] [] hsplit)
          exact False.elim
            (child.angles_nonempty hchildAngles)
      | cons b bs =>
          have hsplit' :
              C.rays =
                deletedParentRay r i hir :: b :: bs := by
            simpa using hsplit
          exact centreExponent_mono_delete_first_ray
            C hir hother b bs hsplit' ht
  | cons first mid =>
      cases post with
      | nil =>
          have hsplit' :
              C.rays =
                first :: (mid ++
                  [deletedParentRay r i hir]) := by
            simpa [List.append_assoc] using hsplit
          exact centreExponent_mono_delete_last_ray
            C hir hother first mid hsplit' ht
      | cons next tail =>
          have hsplit' :
              C.rays =
                first :: (mid ++
                  deletedParentRay r i hir :: next :: tail) := by
            simpa [List.append_assoc] using hsplit
          exact centreExponent_mono_delete_interior_ray
            C hir hother first mid next tail hsplit' ht

#print axioms listExponent_merge_mono
#print axioms listExponent_delete_first_general_mono
#print axioms listExponent_delete_interior_mono
#print axioms listExponent_delete_last_mono
#print axioms centreExponent_mono_delete_first_ray
#print axioms centreExponent_mono_delete_interior_ray
#print axioms centreExponent_mono_delete_last_ray
#print axioms centreExponent_mono_restrictDelete

end JSP000404Research
