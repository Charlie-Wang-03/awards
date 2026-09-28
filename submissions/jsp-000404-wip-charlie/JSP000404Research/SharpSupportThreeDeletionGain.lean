import JSP000404Research.SharpPinnedSupportThreeShape
import JSP000404Research.ConcreteCentreDeletionGain
import Mathlib.Tactic

/-!
# Deleting the sharp pinned ray at a support-three centre gains one exponent

At a deficit-three support-three centre, pin the ray pointing to a sharp
vertex s.  SharpPinnedSupportThreeShape shows that the two cyclic quotients
adjacent to this ray are both positive.

The strengthened pinned-shape interface retains the canonical split

  rays = pre ++ (i->s) :: post

and the exact rotation cut k=|pre|.  This file performs the remaining list
bookkeeping.  In the three possible canonical positions of the deleted ray
(first, interior, last), the positive first/last quotients of the rotated list
are exactly the two parent quotients merged by concrete deletion.

Therefore deleting the sharp vertex raises the surviving support-three centre
exponent by at least one.
-/

namespace JSP000404Research

open Real

/-- Main concrete sharp-ray deletion gain. -/
theorem sharp_support_three_delete_sharp_gain
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : 3 ≤ Fintype.card V)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s i : V}
    (hsi : s ≠ i)
    (hs : SharpAt p delta lam s)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3) :
    let hir : i ≠ s := hsi.symm
    let hother :=
      child_other_nonempty_of_card_ge_three hcard hir
    centreExponent C t + 1 ≤
      centreExponent (C.restrictDelete s hir hother) t := by
  let hir : i ≠ s := hsi.symm
  let hother :=
    child_other_nonempty_of_card_ge_three hcard hir
  let del : OtherVertex i := deletedParentRay s i hir

  obtain ⟨first0, rest0, k, pre, post, r, rest,
      qFirst, qLast, qmid,
      _hrays0, hsplit, hk, _hrotRays, hqrot,
      hFirst, hLast, _hmidCount, _hmidLen, _hmass, _hangles⟩ :=
    exists_sharp_pinned_support_three_shape_with_split
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsi hs C hexp hsupport

  have hsplitDel :
      C.rays = pre ++ del :: post := by
    simpa [del, deletedParentRay, hir] using hsplit

  let qs := quotientList t C.gaps
  have hqrot' :
      qs.rotate pre.length =
        qFirst :: qmid ++ [qLast] := by
    dsimp [qs]
    rw [← hk]
    exact hqrot

  have ht0 : 0 ≤ t := by
    exact (sendov_scale_pos
      (by omega : 1 ≤ n) hdelta0 ht).le

  cases pre with
  | nil =>
      cases post with
      | nil =>
          have hrotLen :
              (C.rays.rotate k).length = 1 := by
            rw [List.length_rotate, hsplit]
            simp
          have hshapeLen :
              (C.rays.rotate k).length ≥ 2 := by
            rw [_hrotRays]
            simp
          omega
      | cons next tail =>
          have hsplitFirst :
              C.rays = del :: next :: tail := by
            simpa using hsplitDel
          let a := rayThetaAt hp i del
          let b := rayThetaAt hp i next
          let bs := tail.map (rayThetaAt hp i)
          let qRight :=
            Nat.floor (t * firstNormalizedGap a b)
          let qWrap :=
            Nat.floor (t * lastNormalizedGap a b bs)
          let middle :=
            quotientList t (normalizedSuccessiveTail b bs)
          have hParentAngles :
              C.angles = a :: b :: bs := by
            simp [CentreProjectiveCycle.angles,
              hsplitFirst, a, b, bs]
          have hqParent :
              qs = qRight :: (middle ++ [qWrap]) := by
            dsimp [qs]
            rw [CentreProjectiveCycle.gaps, hParentAngles]
            simpa [qRight, qWrap, middle] using
              quotientList_cons_cons_parent t a b bs
          have hqrot0 :
              qs = qFirst :: qmid ++ [qLast] := by
            simpa using hqrot'
          have hcons :
              qRight :: (middle ++ [qWrap]) =
                qFirst :: (qmid ++ [qLast]) := by
            rw [← hqParent, hqrot0]
          have hRightEq : qRight = qFirst :=
            (List.cons.inj hcons).1
          have htailEq :
              middle ++ [qWrap] =
                qmid ++ [qLast] :=
            (List.cons.inj hcons).2
          have hLastEq : qWrap = qLast := by
            have h :=
              congrArg (fun l => l.getLastD 0) htailEq
            simpa using h
          have hRightPos : 1 ≤ qRight := by
            rw [hRightEq]
            exact hFirst
          have hWrapPos : 1 ≤ qWrap := by
            rw [hLastEq]
            exact hLast
          have hRightGeom :
              qRight =
                Nat.floor
                  (t * ((rayThetaAt hp i next -
                    rayThetaAt hp i del) / Real.pi)) := by
            rfl
          have hWrapGeom :
              qWrap =
                Nat.floor
                  (t * ((rayThetaAt hp i del + Real.pi -
                    (tail.map (rayThetaAt hp i)).getLastD
                      (rayThetaAt hp i next)) / Real.pi)) := by
            rfl
          exact centreExponent_gain_delete_first_ray
            C hir hother next tail hsplitFirst ht0
            (by simpa [hRightGeom] using hRightPos)
            (by simpa [hWrapGeom] using hWrapPos)

  | cons first mid =>
      cases post with
      | nil =>
          have hsplitLast :
              C.rays = first :: (mid ++ [del]) := by
            simpa [List.append_assoc] using hsplitDel
          let a := rayThetaAt hp i first
          let preA := mid.map (rayThetaAt hp i)
          let x := rayThetaAt hp i del
          let prefix := quotientList t (normalizedPrefixGaps a preA)
          let qLeft :=
            Nat.floor
              (t * ((x - preA.getLastD a) / Real.pi))
          let qWrap :=
            Nat.floor
              (t * ((a + Real.pi - x) / Real.pi))
          have hParentAngles :
              C.angles = a :: (preA ++ [x]) := by
            simp [CentreProjectiveCycle.angles,
              hsplitLast, a, preA, x]
          have hqParent :
              qs = prefix ++ [qLeft, qWrap] := by
            dsimp [qs]
            rw [CentreProjectiveCycle.gaps, hParentAngles,
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
                qFirst :: (qmid ++ [qLast]) := by
            rw [← hrotParent]
            simpa using hqrot'
          have hWrapEq : qWrap = qFirst :=
            (List.cons.inj hrotEq).1
          have htailEq :
              prefix ++ [qLeft] =
                qmid ++ [qLast] :=
            (List.cons.inj hrotEq).2
          have hLeftEq : qLeft = qLast := by
            have h :=
              congrArg (fun l => l.getLastD 0) htailEq
            simpa using h
          have hLeftPos : 1 ≤ qLeft := by
            rw [hLeftEq]
            exact hLast
          have hWrapPos : 1 ≤ qWrap := by
            rw [hWrapEq]
            exact hFirst
          exact centreExponent_gain_delete_last_ray
            C hir hother first mid hsplitLast ht0
            (by simpa [qLeft, preA, a, x] using hLeftPos)
            (by simpa [qWrap, a, x] using hWrapPos)

      | cons next tail =>
          have hsplitInterior :
              C.rays =
                first :: (mid ++ del :: next :: tail) := by
            simpa [List.append_assoc] using hsplitDel
          let a := rayThetaAt hp i first
          let preA := mid.map (rayThetaAt hp i)
          let x := rayThetaAt hp i del
          let y := rayThetaAt hp i next
          let tailA := tail.map (rayThetaAt hp i)
          let prefix := quotientList t (normalizedPrefixGaps a preA)
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
          have hParentAngles :
              C.angles =
                a :: (preA ++ x :: y :: tailA) := by
            simp [CentreProjectiveCycle.angles,
              hsplitInterior, a, preA, x, y, tailA]
          have hqParent :
              qs =
                prefix ++ [qLeft, qRight] ++ suffix := by
            dsimp [qs]
            rw [CentreProjectiveCycle.gaps, hParentAngles,
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
                qRight :: (suffix ++ prefix ++ [qLeft]) := by
            rw [hqRegroup, hkLen]
            rw [List.rotate_append_length_eq]
            simp [List.append_assoc]
          have hrotEq :
              qRight :: (suffix ++ prefix ++ [qLeft]) =
                qFirst :: (qmid ++ [qLast]) := by
            rw [← hrotParent]
            simpa using hqrot'
          have hRightEq : qRight = qFirst :=
            (List.cons.inj hrotEq).1
          have htailEq :
              suffix ++ prefix ++ [qLeft] =
                qmid ++ [qLast] :=
            (List.cons.inj hrotEq).2
          have hLeftEq : qLeft = qLast := by
            have h :=
              congrArg (fun l => l.getLastD 0) htailEq
            simpa [List.append_assoc] using h
          have hLeftPos : 1 ≤ qLeft := by
            rw [hLeftEq]
            exact hLast
          have hRightPos : 1 ≤ qRight := by
            rw [hRightEq]
            exact hFirst
          exact centreExponent_gain_delete_interior_ray
            C hir hother first mid next tail
            hsplitInterior ht0
            (by simpa [qLeft, preA, a, x] using hLeftPos)
            (by simpa [qRight, x, y] using hRightPos)

#print axioms sharp_support_three_delete_sharp_gain

end JSP000404Research
