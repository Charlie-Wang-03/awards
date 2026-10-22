import JSP000404Research.SharpPinnedSupportThreeShape
import JSP000404Research.SixPointSupportThreeShape
import JSP000404Research.SupportThreeLeftHiddenDeletionGain
import JSP000404Research.SupportThreeRightHiddenDeletionGain
import Mathlib.Tactic

/-!
# Actual six-point support-three: middle obstruction or concrete non-top deletion

This lemma composes the sharp-pinned genuine AngleCap quotient classification
with both concrete one-step non-top deletion gains. In the six-original-vertex
terminal, the middle hidden positive quotient [0,q,0] is the ONLY branch
not paid by a local non-top deletion from this support-three centre.

Crucially the statement preserves the actual deleted original vertex and
the actual restricted CentreProjectiveCycle, rather than an abstract cyclic
index or a conditional deletion in a fabricated list.

It does NOT exclude the exceptional middle shape and does NOT prove a
global simultaneous six-source payment. It is a local structural advance.
-/

namespace JSP000404Research

theorem six_point_support_three_middle_or_concrete_nonTop_gain
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (ht0 : 0 ≤ t)
    {s i : V}
    (hsi : s ≠ i)
    (hs : SharpAt p delta lam s)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 3)
    (hsupport : positiveSupport (centreQuotient C t) = 3) :
    (∃ first0 : OtherVertex i,
       ∃ rest0 : List (OtherVertex i),
       ∃ k : ℕ,
       ∃ r : OtherVertex i,
       ∃ rest : List (OtherVertex i),
       ∃ qFirst qLast qHidden : ℕ,
         qHidden ≠ 0 ∧
         C.rays = first0 :: rest0 ∧
         C.rays.rotate k = (⟨s,hsi⟩ : OtherVertex i) :: r :: rest ∧
         (quotientList t C.gaps).rotate k =
           qFirst :: [0,qHidden,0] ++ [qLast])
    ∨
    (∃ deleted : V, ∃ hir : i ≠ deleted,
       deleted ≠ s ∧
       let hother :
           Nonempty (OtherVertex (survivingCentre deleted i hir)) :=
         child_other_nonempty_of_card_ge_three
           (by rw [hcard]; omega) hir
       centreExponent C t + 1 ≤
         centreExponent (C.restrictDelete deleted hir hother) t) := by
  obtain ⟨first0, rest0, k, preTop, postTop, r, rest,
      qFirst, qLast, qmid,
      hrays0, hsplitTop, hk, hrotRays, hqrot,
      hFirst, hLast, hmidCount, _hangleLen,
      _hmass, _hangles⟩ :=
    exists_sharp_pinned_support_three_shape_with_split
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsi hs C hexp hsupport
  have hqLen :
      ((quotientList t C.gaps).rotate k).length = 5 := by
    rw [List.length_rotate, quotientList_length, C.gaps_length,
      centreRayList_length_eq_five_of_card_six C hcard]
  have hmidLen : qmid.length = 3 := by
    rw [hqrot] at hqLen
    simp at hqLen
    omega
  obtain ⟨qHidden, hHidden, hshape⟩ :=
    length_three_positiveCount_one_shape qmid hmidLen hmidCount
  have hH : 1 ≤ qHidden :=
    Nat.one_le_iff_ne_zero.mpr hHidden
  have hrotNodup :
      ((⟨s,hsi⟩ : OtherVertex i) :: r :: rest).Nodup := by
    rw [← hrotRays]
    simpa using C.nodup
  have hrNotTop : r.1 ≠ s := by
    intro heq
    have hray : r = (⟨s,hsi⟩ : OtherVertex i) :=
      Subtype.ext heq
    exact (List.nodup_cons.mp hrotNodup).1 (by simp [hray])
  rcases hshape with hleft | hmiddle | hright
  · right
    have hgain :=
      support_three_left_hidden_nonTop_deletion_gain
        hp hcard hsi C first0 rest0 k
        preTop postTop r rest qFirst qLast qHidden
        hrays0 hsplitTop hk hrotRays
        (by simpa [hleft] using hqrot)
        hFirst hH ht0
    refine ⟨r.1, r.2.symm, hrNotTop, ?_⟩
    simpa using hgain
  · left
    exact ⟨first0, rest0, k, r, rest,
      qFirst, qLast, qHidden,
      hHidden, hrays0, hrotRays,
      by simpa [hmiddle] using hqrot⟩
  · right
    exact support_three_right_hidden_has_nonTop_deletion_gain
      hp hcard hsi C k preTop postTop r rest qFirst qLast qHidden
      hsplitTop hk hrotRays
      (by simpa [hright] using hqrot)
      hLast hH ht0

#print axioms six_point_support_three_middle_or_concrete_nonTop_gain

end JSP000404Research
