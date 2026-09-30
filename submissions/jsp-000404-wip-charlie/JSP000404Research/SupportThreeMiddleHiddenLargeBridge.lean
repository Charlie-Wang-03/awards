import JSP000404Research.PositiveTransitionAngleAlignment
import JSP000404Research.SupportThreeMiddleOrDeletionGain
import JSP000404Research.SixPointSupportThreeShape
import JSP000404Research.ConcreteDeficitThree
import JSP000404Research.CyclicEdgeRotation
import Mathlib.Tactic

/-!
# Large hidden bridge in the middle-hidden support-three terminal

Assume a six-point deficit-three/support-three centre is in the pinned
middle-hidden shape

  rays      = [top, r, b, c, d]
  quotients = [qFirst, 0, qHidden, 0, qLast]

after the same cyclic rotation, and that the centre has three sign
transitions.

Support three plus quotient sum n makes every positive quotient at most n-2.
Saturation of the transition count says every positive quotient is a sign
transition.  The positionwise large-angle theorem is cyclically invariant, so
at the hidden positive slot we obtain

  (1+delta)*lambda < angle(b, centre, c).

This is the missing quantitative information discarded by the earlier
small-perfect-matching abstraction.
-/

namespace JSP000404Research

open Real

theorem support_three_middle_hidden_large_bridge
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : CentreProjectiveCycle hp i)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {top i : V}
    (hit : i ≠ top)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3)
    (hmiddle :
      SupportThreePinnedMiddleShape hp
        (show top ≠ i by simpa using hit) C)
    (hthree :
      ∃ first rest,
        C.rays = first :: rest ∧
        boolTransitionCountFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest) = 3) :
    ∃ r b c d : OtherVertex i,
      r.1 ≠ top ∧ b.1 ≠ top ∧
      c.1 ≠ top ∧ d.1 ≠ top ∧
      r ≠ b ∧ r ≠ c ∧ r ≠ d ∧
      b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      EuclideanGeometry.angle (p r.1) (p i) (p b.1) +
          EuclideanGeometry.angle (p c.1) (p i) (p d.1)
        ≤ delta * lam ∧
      (1 + delta) * lam <
        EuclideanGeometry.angle (p top) (p i) (p r.1) ∧
      (1 + delta) * lam <
        EuclideanGeometry.angle (p b.1) (p i) (p c.1) ∧
      (1 + delta) * lam <
        EuclideanGeometry.angle (p d.1) (p i) (p top) := by
  classical
  obtain ⟨first0, rest0, k, preTop, postTop,
      r, rest, qFirst, qLast, qHidden,
      hrays0, hsplitTop, hk, hrotRays, hqrot,
      hFirst, hLast, hHidden⟩ := hmiddle

  have hlenRays : C.rays.length = 5 := by
    rw [centreRayList_length_eq_card_sub_one C, hcard]
    norm_num
  have hlenRot : (C.rays.rotate k).length = 5 := by
    rw [List.length_rotate, hlenRays]
  rw [hrotRays] at hlenRot
  simp only [List.length_cons] at hlenRot
  have hrestLen : rest.length = 3 := by omega

  obtain ⟨b,c,d,hrest⟩ :
      ∃ b c d : OtherVertex i, rest = [b,c,d] := by
    cases rest with
    | nil => simp at hrestLen
    | cons b rest1 =>
      cases rest1 with
      | nil => simp at hrestLen
      | cons c rest2 =>
        cases rest2 with
        | nil => simp at hrestLen
        | cons d rest3 =>
          have hnil : rest3 = [] := by
            simpa using hrestLen
          subst rest3
          exact ⟨b,c,d,rfl⟩

  let topRay : OtherVertex i := ⟨top, by simpa using hit⟩
  have hrotShape :
      C.rays.rotate k = topRay :: r :: b :: c :: d :: [] := by
    simpa [topRay, hrest] using hrotRays

  have hnodup :
      (topRay :: r :: b :: c :: d :: []).Nodup := by
    rw [← hrotShape]
    simpa using C.nodup
  have htailNodup :
      (r :: b :: c :: d :: []).Nodup :=
    (List.nodup_cons.mp hnodup).2
  have htopNotTail :
      topRay ∉ (r :: b :: c :: d :: []) :=
    (List.nodup_cons.mp hnodup).1

  have hrTop : r.1 ≠ top := by
    intro h
    apply htopNotTail
    left
    apply Subtype.ext
    simpa [topRay] using h.symm
  have hbTop : b.1 ≠ top := by
    intro h
    apply htopNotTail
    right; left
    apply Subtype.ext
    simpa [topRay] using h.symm
  have hcTop : c.1 ≠ top := by
    intro h
    apply htopNotTail
    right; right; left
    apply Subtype.ext
    simpa [topRay] using h.symm
  have hdTop : d.1 ≠ top := by
    intro h
    apply htopNotTail
    right; right; right
    apply Subtype.ext
    simpa [topRay] using h.symm

  have hrb : r ≠ b :=
    (List.nodup_cons.mp htailNodup).1 (by simp)
  have hrc : r ≠ c :=
    (List.nodup_cons.mp htailNodup).1 (by simp)
  have hrd : r ≠ d :=
    (List.nodup_cons.mp htailNodup).1 (by simp)
  have hbcd :
      (b :: c :: d :: []).Nodup :=
    (List.nodup_cons.mp htailNodup).2
  have hbc : b ≠ c :=
    (List.nodup_cons.mp hbcd).1 (by simp)
  have hbd : b ≠ d :=
    (List.nodup_cons.mp hbcd).1 (by simp)
  have hcd : c ≠ d := by
    have hcdN := (List.nodup_cons.mp hbcd).2
    exact (List.nodup_cons.mp hcdN).1 (by simp)

  obtain ⟨firstT,restT,hraysT,htransT⟩ := hthree
  have hrestTLen : restT.length = 4 := by
    have h := hlenRays
    rw [hraysT] at h
    simp at h
    omega
  have hrestT : restT ≠ [] := by
    intro hnil
    rw [hnil] at hrestTLen
    simp at hrestTLen

  have hdelta1 : delta < 1 := by linarith
  have hqsum :
      (quotientList t C.gaps).sum = n :=
    deficit_three_support_three_list_sum
      C hn hdelta0 hdelta1 ht hexp hsupport
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) = 3 := by
    rw [← centreQuotient_ofFn C t,
        listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :
      1 ≤ t :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht

  let AsT : List ℝ :=
    cyclicRayAngles (p := p) i firstT restT
  have hlarge :
      PositiveQuotientAngleGt
        ((1 + delta) * lam)
        (quotientList t C.gaps) AsT := by
    dsimp [AsT]
    exact centre_three_transition_positive_angles_large
      hp hcap (by omega : 2 ≤ n)
      htpos htone ht hlam i C
      firstT restT hraysT hrestT
      htransT hsupportList hqsum

  have hlargeRot :
      PositiveQuotientAngleGt
        ((1 + delta) * lam)
        ((quotientList t C.gaps).rotate k)
        (AsT.rotate k) :=
    positiveQuotientAngleGt_rotate hlarge k

  have hzeroAlign :=
    centre_zeroQuotientAngleAligned
      hp hcap htpos htone hlam i C
      firstT restT hraysT
  have hqALen :
      (quotientList t C.gaps).length = AsT.length := by
    dsimp [AsT]
    exact zeroQuotientAngleAligned_length_q_angle hzeroAlign
  have hmass :
      listZeroAngleMass
          (quotientList t C.gaps) AsT
        ≤ delta * lam := by
    dsimp [AsT]
    exact
      centre_zeroAngleMass_le_delta_lam_of_deficit_three_support_three
        hp hcap hn hdelta0 hdeltaHalf ht hlam
        i C hexp hsupport firstT restT hraysT
  have hmassRot :
      listZeroAngleMass
          ((quotientList t C.gaps).rotate k)
          (AsT.rotate k)
        ≤ delta * lam := by
    rw [listZeroAngleMass_rotate
      (quotientList t C.gaps) AsT hqALen k]
    exact hmass

  let w :=
    fun x y : OtherVertex i =>
      EuclideanGeometry.angle (p x.1) (p i) (p y.1)
  have hAsEdge :
      AsT = cyclicEdgeValues w C.rays := by
    dsimp [AsT, w]
    rw [hraysT]
    exact cyclicRayAngles_eq_cyclicEdgeValues
      (p := p) i firstT restT

  have hAsRot :
      AsT.rotate k =
        cyclicRayAngles (p := p) i topRay (r :: b :: c :: d :: []) := by
    calc
      AsT.rotate k
          = (cyclicEdgeValues w C.rays).rotate k := by rw [hAsEdge]
      _ = cyclicEdgeValues w (C.rays.rotate k) := by
          symm
          exact cyclicEdgeValues_rotate w C.rays k
      _ = cyclicEdgeValues w
            (topRay :: r :: b :: c :: d :: []) := by
          rw [hrotShape]
      _ = cyclicRayAngles (p := p) i topRay
            (r :: b :: c :: d :: []) := by
          symm
          exact cyclicRayAngles_eq_cyclicEdgeValues
            (p := p) i topRay (r :: b :: c :: d :: [])

  have hqShape :
      (quotientList t C.gaps).rotate k =
        qFirst :: 0 :: qHidden :: 0 :: qLast :: [] := by
    simpa [List.append_assoc] using hqrot

  have hAShape :
      AsT.rotate k =
        EuclideanGeometry.angle (p top) (p i) (p r.1) ::
        EuclideanGeometry.angle (p r.1) (p i) (p b.1) ::
        EuclideanGeometry.angle (p b.1) (p i) (p c.1) ::
        EuclideanGeometry.angle (p c.1) (p i) (p d.1) ::
        EuclideanGeometry.angle (p d.1) (p i) (p top) :: [] := by
    rw [hAsRot]
    simp [cyclicRayAngles, consecutiveRayAngles, topRay]

  have hqFirstNe : qFirst ≠ 0 := by omega
  have hqLastNe : qLast ≠ 0 := by omega

  have hsmall :
      EuclideanGeometry.angle (p r.1) (p i) (p b.1) +
          EuclideanGeometry.angle (p c.1) (p i) (p d.1)
        ≤ delta * lam := by
    rw [hqShape, hAShape] at hmassRot
    simpa [listZeroAngleMass, hqFirstNe, hHidden, hqLastNe]
      using hmassRot

  rw [hqShape, hAShape] at hlargeRot
  unfold PositiveQuotientAngleGt at hlargeRot
  cases hlargeRot with
  | cons h0 htail0 =>
    cases htail0 with
    | cons h1 htail1 =>
      cases htail1 with
      | cons h2 htail2 =>
        cases htail2 with
        | cons h3 htail3 =>
          cases htail3 with
          | cons h4 htail4 =>
            have hTopR := h0 hqFirstNe
            have hBridge := h2 hHidden
            have hDTop := h4 hqLastNe
            exact ⟨r,b,c,d,
              hrTop,hbTop,hcTop,hdTop,
              hrb,hrc,hrd,hbc,hbd,hcd,
              hsmall,hTopR,hBridge,hDTop⟩

#print axioms support_three_middle_hidden_large_bridge

end JSP000404Research
