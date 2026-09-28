import JSP000404Research.ConcreteDeletionStableSplit
import JSP000404Research.GeneralProjectiveGapDeletion
import JSP000404Research.PinnedCycleRotation
import Mathlib.Tactic

/-!
# Cyclic positive-positive ray implies concrete deletion gain

Suppose a concrete centre ray list is split at the ray to be deleted,

  C.rays = pre ++ deletedRay :: post.

Rotating the aligned cyclic quotient list by |pre| puts the outgoing quotient
of deletedRay first and its incoming quotient last.  Therefore, if

  (quotientList t C.gaps).rotate pre.length
    = qOut :: qmid ++ [qIn]

with qOut,qIn positive, the deleted ray is flanked by positive quotients in
the canonical parent cycle.

This file packages the list bookkeeping once.  Combined with
ConcreteCentreDeletionGain, it yields a position-independent concrete
deletion-gain theorem.
-/

namespace JSP000404Research

open Real

/-- Rotated first/last quotient positivity is exactly the concrete
positive-positive adjacency condition at the split ray. -/
theorem parentSplitBothAdjacentPositive_of_rotated_ends
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    (C : CentreProjectiveCycle hp i)
    (hir : i ≠ r)
    (pre post : List (OtherVertex i))
    (hsplit :
      C.rays =
        pre ++ deletedParentRay r i hir :: post)
    {t : ℝ}
    (qOut qIn : ℕ)
    (qmid : List ℕ)
    (hqrot :
      (quotientList t C.gaps).rotate pre.length =
        qOut :: qmid ++ [qIn])
    (hOut : 1 ≤ qOut)
    (hIn : 1 ≤ qIn) :
    ParentSplitBothAdjacentPositive C hir pre post t := by
  let del := deletedParentRay r i hir
  let qs := quotientList t C.gaps

  cases pre with
  | nil =>
      cases post with
      | nil =>
          have hqLen :
              qs.length = 1 := by
            dsimp [qs]
            rw [quotientList_length, C.gaps_length, hsplit]
            simp
          have hrotLen :
              (qs.rotate 0).length =
                (qOut :: qmid ++ [qIn]).length :=
            congrArg List.length hqrot
          rw [List.length_rotate, hqLen] at hrotLen
          simp at hrotLen
          omega
      | cons b bs =>
          have hrays :
              C.rays = del :: b :: bs := by
            simpa [del] using hsplit
          let a := rayThetaAt hp i del
          let bb := rayThetaAt hp i b
          let tail := bs.map (rayThetaAt hp i)
          let qRight :=
            Nat.floor (t * firstNormalizedGap a bb)
          let qWrap :=
            Nat.floor (t * lastNormalizedGap a bb tail)
          let middle :=
            quotientList t (normalizedSuccessiveTail bb tail)

          have hAngles :
              C.angles = a :: bb :: tail := by
            simp [CentreProjectiveCycle.angles, hrays,
              a, bb, tail, del]
          have hqParent :
              qs = qRight :: (middle ++ [qWrap]) := by
            dsimp [qs]
            rw [CentreProjectiveCycle.gaps, hAngles]
            simpa [qRight, qWrap, middle] using
              quotientList_cons_cons_parent t a bb tail
          have hqEq :
              qs = qOut :: qmid ++ [qIn] := by
            simpa using hqrot
          have hfirst :
              qRight = qOut := by
            rw [hqParent] at hqEq
            exact (List.cons.inj hqEq).1
          have hlast :
              qWrap = qIn := by
            rw [hqParent] at hqEq
            have h :=
              congrArg (fun l => l.getLastD 0) hqEq
            simpa using h
          have hRight : 1 ≤ qRight := by
            rw [hfirst]
            exact hOut
          have hWrap : 1 ≤ qWrap := by
            rw [hlast]
            exact hIn
          simp only [ParentSplitBothAdjacentPositive]
          constructor
          · simpa [qRight, firstNormalizedGap, a, bb, del]
              using hRight
          · simpa [qWrap, lastNormalizedGap, a, bb, tail, del]
              using hWrap

  | cons first mid =>
      cases post with
      | nil =>
          have hrays :
              C.rays =
                first :: (mid ++ [del]) := by
            simpa [List.append_assoc, del] using hsplit
          let a := rayThetaAt hp i first
          let preA := mid.map (rayThetaAt hp i)
          let x := rayThetaAt hp i del
          let prefix :=
            quotientList t (normalizedPrefixGaps a preA)
          let qLeft :=
            Nat.floor
              (t * ((x - preA.getLastD a) / Real.pi))
          let qWrap :=
            Nat.floor
              (t * ((a + Real.pi - x) / Real.pi))

          have hAngles :
              C.angles = a :: (preA ++ [x]) := by
            simp [CentreProjectiveCycle.angles, hrays,
              a, preA, x, del]
          have hqParent :
              qs = prefix ++ [qLeft, qWrap] := by
            dsimp [qs]
            rw [CentreProjectiveCycle.gaps, hAngles,
              normalizedProjectiveGaps_last_parent]
            simp [prefix, qLeft, qWrap,
              quotientList, List.map_append]

          have hkLen :
              (first :: mid).length =
                (prefix ++ [qLeft]).length := by
            dsimp [prefix, preA]
            simp [quotientList, normalizedPrefixGaps,
              successiveDiffsFrom_length]
          have hrotParent :
              qs.rotate (first :: mid).length =
                qWrap :: (prefix ++ [qLeft]) := by
            rw [hqParent, hkLen]
            rw [List.rotate_append_length_eq]
            simp [List.append_assoc]
          have hrotEq :
              qWrap :: (prefix ++ [qLeft]) =
                qOut :: qmid ++ [qIn] := by
            rw [← hrotParent]
            simpa using hqrot
          have hwrapEq : qWrap = qOut :=
            (List.cons.inj hrotEq).1
          have htailEq :
              prefix ++ [qLeft] =
                qmid ++ [qIn] :=
            (List.cons.inj hrotEq).2
          have hleftEq : qLeft = qIn := by
            have h :=
              congrArg (fun l => l.getLastD 0) htailEq
            simpa using h
          have hLeft : 1 ≤ qLeft := by
            rw [hleftEq]
            exact hIn
          have hWrap : 1 ≤ qWrap := by
            rw [hwrapEq]
            exact hOut
          simp only [ParentSplitBothAdjacentPositive]
          constructor
          · simpa [qLeft, preA, a, x, del] using hLeft
          · simpa [qWrap, a, x, del] using hWrap

      | cons next tail =>
          have hrays :
              C.rays =
                first ::
                  (mid ++ del :: next :: tail) := by
            simpa [List.append_assoc, del] using hsplit
          let a := rayThetaAt hp i first
          let preA := mid.map (rayThetaAt hp i)
          let x := rayThetaAt hp i del
          let y := rayThetaAt hp i next
          let tailA := tail.map (rayThetaAt hp i)
          let prefix :=
            quotientList t (normalizedPrefixGaps a preA)
          let suffix :=
            quotientList t (normalizedSuffixGaps y tailA) ++
              [Nat.floor
                (t * ((a + Real.pi -
                  tailA.getLastD y) / Real.pi))]
          let qLeft :=
            Nat.floor
              (t * ((x - preA.getLastD a) / Real.pi))
          let qRight :=
            Nat.floor
              (t * ((y - x) / Real.pi))

          have hAngles :
              C.angles =
                a :: (preA ++ x :: y :: tailA) := by
            simp [CentreProjectiveCycle.angles,
              hrays, a, preA, x, y, tailA]
          have hqParent :
              qs =
                prefix ++ [qLeft, qRight] ++ suffix := by
            dsimp [qs]
            rw [CentreProjectiveCycle.gaps, hAngles,
              normalizedProjectiveGaps_interior_parent]
            simp [prefix, suffix, qLeft, qRight,
              quotientList, List.map_append,
              List.append_assoc]

          have hkLen :
              (first :: mid).length =
                (prefix ++ [qLeft]).length := by
            dsimp [prefix, preA]
            simp [quotientList, normalizedPrefixGaps,
              successiveDiffsFrom_length]
          have hqRegroup :
              qs =
                (prefix ++ [qLeft]) ++
                  qRight :: suffix := by
            rw [hqParent]
            simp [List.append_assoc]
          have hrotParent :
              qs.rotate (first :: mid).length =
                qRight ::
                  (suffix ++ prefix ++ [qLeft]) := by
            rw [hqRegroup, hkLen]
            rw [List.rotate_append_length_eq]
            simp [List.append_assoc]
          have hrotEq :
              qRight ::
                  (suffix ++ prefix ++ [qLeft]) =
                qOut :: qmid ++ [qIn] := by
            rw [← hrotParent]
            simpa using hqrot
          have hrightEq : qRight = qOut :=
            (List.cons.inj hrotEq).1
          have htailEq :
              suffix ++ prefix ++ [qLeft] =
                qmid ++ [qIn] :=
            (List.cons.inj hrotEq).2
          have hleftEq : qLeft = qIn := by
            have h :=
              congrArg (fun l => l.getLastD 0) htailEq
            simpa [List.append_assoc] using h
          have hLeft : 1 ≤ qLeft := by
            rw [hleftEq]
            exact hIn
          have hRight : 1 ≤ qRight := by
            rw [hrightEq]
            exact hOut
          simp only [ParentSplitBothAdjacentPositive]
          constructor
          · simpa [qLeft, preA, a, x, del] using hLeft
          · simpa [qRight, x, y, del] using hRight

/-- Position-free concrete deletion gain from a rotated cyclic quotient
witness whose first and last entries are positive. -/
theorem centreExponent_gain_delete_of_rotated_positive_ends
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
    (qOut qIn : ℕ)
    (qmid : List ℕ)
    (hqrot :
      (quotientList t C.gaps).rotate pre.length =
        qOut :: qmid ++ [qIn])
    (hOut : 1 ≤ qOut)
    (hIn : 1 ≤ qIn) :
    centreExponent C t + 1 ≤
      centreExponent
        (C.restrictDelete r hir hother) t := by
  have hboth :=
    parentSplitBothAdjacentPositive_of_rotated_ends
      C hir pre post hsplit
      qOut qIn qmid hqrot hOut hIn
  cases pre with
  | nil =>
      cases post with
      | nil =>
          simp [ParentSplitBothAdjacentPositive] at hboth
      | cons b bs =>
          have hrays :
              C.rays =
                deletedParentRay r i hir :: b :: bs := by
            simpa using hsplit
          exact centreExponent_gain_delete_first_ray
            C hir hother b bs hrays ht
            hboth.1 hboth.2
  | cons first mid =>
      cases post with
      | nil =>
          have hrays :
              C.rays =
                first :: (mid ++
                  [deletedParentRay r i hir]) := by
            simpa [List.append_assoc] using hsplit
          exact centreExponent_gain_delete_last_ray
            C hir hother first mid hrays ht
            hboth.1 hboth.2
      | cons next tail =>
          have hrays :
              C.rays =
                first :: (mid ++
                  deletedParentRay r i hir :: next :: tail) := by
            simpa [List.append_assoc] using hsplit
          exact centreExponent_gain_delete_interior_ray
            C hir hother first mid next tail
            hrays ht hboth.1 hboth.2

#print axioms parentSplitBothAdjacentPositive_of_rotated_ends
#print axioms centreExponent_gain_delete_of_rotated_positive_ends

end JSP000404Research
