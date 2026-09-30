import JSP000404Research.SupportThreeLeftHiddenDeletionGain
import JSP000404Research.SupportThreeRightHiddenDeletionGain
import JSP000404Research.SixPointSupportThreeShape
import Mathlib.Tactic

/-!
# Middle-hidden or a compensating non-top deletion gain

For a six-point n-3/support-three centre pinned at the sharp top, the hidden
positive quotient has exactly three possible middle positions:

  [qHidden,0,0], [0,qHidden,0], [0,0,qHidden].

The two end positions have now been lifted to concrete non-top deletion gains.
Therefore every such support-three centre satisfies a clean dichotomy:

* either its pinned quotient cycle has the unique middle-hidden form
    qFirst :: [0,qHidden,0] ++ [qLast],
* or deleting some non-top vertex raises this centre exponent by one.

This is the structural reduction needed by compensated minimum deletion.
-/

namespace JSP000404Research

def SupportThreePinnedMiddleShape
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {t : ℝ}
    {s i : V}
    (hsi : s ≠ i)
    (C : CentreProjectiveCycle hp i) : Prop :=
  ∃ first0 : OtherVertex i,
    ∃ rest0 : List (OtherVertex i),
    ∃ k : ℕ,
    ∃ preTop postTop : List (OtherVertex i),
    ∃ r : OtherVertex i,
    ∃ rest : List (OtherVertex i),
    ∃ qFirst qLast qHidden : ℕ,
      C.rays = first0 :: rest0 ∧
      C.rays =
        preTop ++ (⟨s,hsi⟩ : OtherVertex i) :: postTop ∧
      k = preTop.length ∧
      C.rays.rotate k =
        (⟨s,hsi⟩ : OtherVertex i) :: r :: rest ∧
      (quotientList t C.gaps).rotate k =
        qFirst :: [0,qHidden,0] ++ [qLast] ∧
      1 ≤ qFirst ∧
      1 ≤ qLast ∧
      qHidden ≠ 0

theorem support_three_pinned_middle_or_nonTop_deletion_gain
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 6)
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
    SupportThreePinnedMiddleShape hp hsi C
      ∨
    ∃ deleted : V, ∃ hir : i ≠ deleted,
      deleted ≠ s ∧
      let hother :
          Nonempty (OtherVertex (survivingCentre deleted i hir)) :=
        child_other_nonempty_of_card_ge_three
          (by rw [hcard]; omega) hir
      centreExponent C t + 1 ≤
        centreExponent (C.restrictDelete deleted hir hother) t := by
  obtain ⟨first0, rest0, k, preTop, postTop, r, rest,
      qFirst, qLast, qmid,
      hrays0, hsplitTop, hk, hrotRays, hqrot,
      hFirst, hLast, hmidCount, _hmidAngleLen,
      _hmass, _hangles⟩ :=
    exists_sharp_pinned_support_three_shape_with_split
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsi hs C hexp hsupport

  have hqLen :
      ((quotientList t C.gaps).rotate k).length = 5 := by
    rw [List.length_rotate, quotientList_length, C.gaps_length,
      centreRayList_length_eq_card_sub_one C, hcard]
    norm_num
  have hmidLen : qmid.length = 3 := by
    rw [hqrot] at hqLen
    simp at hqLen
    omega

  obtain ⟨qHidden, hHidden, hshape⟩ :=
    length_three_positiveCount_one_shape
      qmid hmidLen hmidCount
  have hHiddenPos : 1 ≤ qHidden :=
    Nat.one_le_iff_ne_zero.mpr hHidden

  rcases hshape with hleft | hmid | hright
  · right
    have hqLeft :
        (quotientList t C.gaps).rotate k =
          qFirst :: [qHidden,0,0] ++ [qLast] := by
      rw [hqrot, hleft]
    have hgain :=
      support_three_left_hidden_nonTop_deletion_gain
        hp hcard hsi C first0 rest0 k preTop postTop
        r rest qFirst qLast qHidden
        hrays0 hsplitTop hk hrotRays hqLeft
        hFirst hHiddenPos
        (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht).le

    let deleted := r.1
    let hir : i ≠ deleted := r.2
    have hrotNodup :
        ((⟨s,hsi⟩ : OtherVertex i) :: r :: rest).Nodup := by
      rw [← hrotRays]
      simpa using C.nodup
    have hrs :
        (⟨s,hsi⟩ : OtherVertex i) ≠ r :=
      (List.nodup_cons.mp hrotNodup).1 (by simp)
    have hdelTop : deleted ≠ s := by
      intro h
      apply hrs
      apply Subtype.ext
      exact h.symm
    refine ⟨deleted, hir, hdelTop, ?_⟩
    simpa [deleted, hir] using hgain

  · left
    refine ⟨first0, rest0, k, preTop, postTop,
      r, rest, qFirst, qLast, qHidden,
      hrays0, hsplitTop, hk, hrotRays, ?_,
      hFirst, hLast, hHidden⟩
    rw [hqrot, hmid]

  · right
    have hqRight :
        (quotientList t C.gaps).rotate k =
          qFirst :: [0,0,qHidden] ++ [qLast] := by
      rw [hqrot, hright]
    obtain ⟨deleted, hir, hdelTop, hgain⟩ :=
      support_three_right_hidden_has_nonTop_deletion_gain
        hp hcard hsi C k preTop postTop r rest
        qFirst qLast qHidden
        hsplitTop hk hrotRays hqRight
        hLast hHiddenPos
        (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht).le
    exact Or.inr ⟨deleted, hir, hdelTop, hgain⟩

#print axioms SupportThreePinnedMiddleShape
#print axioms support_three_pinned_middle_or_nonTop_deletion_gain

end JSP000404Research
