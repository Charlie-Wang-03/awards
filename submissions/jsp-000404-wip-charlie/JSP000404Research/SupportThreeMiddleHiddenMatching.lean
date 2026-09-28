import JSP000404Research.SupportThreeMiddleOrDeletionGain
import JSP000404Research.FullQuotientZeroAngleMass
import JSP000404Research.CyclicActualAngles
import JSP000404Research.CyclicEdgeRotation
import Mathlib.Tactic

/-!
# Two disjoint small-angle edges in the middle-hidden support-three shape

In the six-point hard branch every surviving support-three minimum has the
pinned quotient shape

  [qFirst, 0, qHidden, 0, qLast]

after rotating the ray to the sharp top to the head.

Since the centre has exponent n-3 and support three, the total actual-angle
mass carried by quotient-zero positions is at most delta*lambda.  In the
middle-hidden shape the only zero positions are the two displayed internal
zeros.  Therefore the four non-top/non-centre vertices occur cyclically as

  a,b,c,d

and satisfy

  angle(a,i,b) + angle(c,i,d) <= delta*lambda.

The five displayed rays are nodup, so a,b,c,d are pairwise distinct and all
avoid the sharp top.
-/

namespace JSP000404Research

open Real

theorem support_three_middle_hidden_small_matching
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
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
        (show top ≠ i by simpa using hit) C) :
    ∃ a b c d : OtherVertex i,
      a.1 ≠ top ∧ b.1 ≠ top ∧
      c.1 ≠ top ∧ d.1 ≠ top ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧
      b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      EuclideanGeometry.angle (p a.1) (p i) (p b.1) +
        EuclideanGeometry.angle (p c.1) (p i) (p d.1)
        ≤ delta * lam := by
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
    simp only [List.mem_cons, List.mem_singleton]
    left
    apply Subtype.ext
    simpa [topRay] using h.symm
  have hbTop : b.1 ≠ top := by
    intro h
    apply htopNotTail
    simp only [List.mem_cons, List.mem_singleton]
    right; left
    apply Subtype.ext
    simpa [topRay] using h.symm
  have hcTop : c.1 ≠ top := by
    intro h
    apply htopNotTail
    simp only [List.mem_cons, List.mem_singleton]
    right; right; left
    apply Subtype.ext
    simpa [topRay] using h.symm
  have hdTop : d.1 ≠ top := by
    intro h
    apply htopNotTail
    simp only [List.mem_cons, List.mem_singleton]
    right; right; right
    apply Subtype.ext
    simpa [topRay] using h.symm

  have hrb : r ≠ b := by
    exact (List.nodup_cons.mp htailNodup).1 (by simp)
  have hrc : r ≠ c := by
    exact (List.nodup_cons.mp htailNodup).1 (by simp)
  have hrd : r ≠ d := by
    exact (List.nodup_cons.mp htailNodup).1 (by simp)
  have hbcd :
      (b :: c :: d :: []).Nodup :=
    (List.nodup_cons.mp htailNodup).2
  have hbc : b ≠ c := by
    exact (List.nodup_cons.mp hbcd).1 (by simp)
  have hbd : b ≠ d := by
    exact (List.nodup_cons.mp hbcd).1 (by simp)
  have hcd : c ≠ d := by
    have hcdN := (List.nodup_cons.mp hbcd).2
    exact (List.nodup_cons.mp hcdN).1 (by simp)

  let qs : List ℕ := quotientList t C.gaps
  let As0 : List ℝ :=
    cyclicRayAngles (p := p) i first0 rest0

  have hqALen : qs.length = As0.length := by
    dsimp [qs, As0]
    rw [quotientList_length, C.gaps_length,
      cyclicRayAngles_length]
    simpa [hrays0]

  have hmass :
      listZeroAngleMass qs As0 ≤ delta * lam := by
    dsimp [qs, As0]
    exact
      centre_zeroAngleMass_le_delta_lam_of_deficit_three_support_three
        hp hcap hn hdelta0 hdeltaHalf ht hlam
        i C hexp hsupport first0 rest0 hrays0

  have hmassRot :
      listZeroAngleMass (qs.rotate k) (As0.rotate k)
        ≤ delta * lam := by
    rw [listZeroAngleMass_rotate qs As0 hqALen k]
    exact hmass

  let w :=
    fun x y : OtherVertex i =>
      EuclideanGeometry.angle (p x.1) (p i) (p y.1)
  have hAsEdge :
      As0 = cyclicEdgeValues w C.rays := by
    dsimp [As0, w]
    rw [hrays0]
    exact cyclicRayAngles_eq_cyclicEdgeValues
      (p := p) i first0 rest0

  have hAsRot :
      As0.rotate k =
        cyclicRayAngles (p := p) i topRay (r :: b :: c :: d :: []) := by
    calc
      As0.rotate k
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
      qs.rotate k =
        qFirst :: 0 :: qHidden :: 0 :: qLast :: [] := by
    dsimp [qs]
    simpa [List.append_assoc] using hqrot

  have hAShape :
      As0.rotate k =
        EuclideanGeometry.angle (p top) (p i) (p r.1) ::
        EuclideanGeometry.angle (p r.1) (p i) (p b.1) ::
        EuclideanGeometry.angle (p b.1) (p i) (p c.1) ::
        EuclideanGeometry.angle (p c.1) (p i) (p d.1) ::
        EuclideanGeometry.angle (p d.1) (p i) (p top) :: [] := by
    rw [hAsRot]
    simp [cyclicRayAngles, consecutiveRayAngles, topRay]

  have hqFirstNe : qFirst ≠ 0 := by omega
  have hqLastNe : qLast ≠ 0 := by omega
  have hmassEq :
      listZeroAngleMass (qs.rotate k) (As0.rotate k)
        =
      EuclideanGeometry.angle (p r.1) (p i) (p b.1) +
        EuclideanGeometry.angle (p c.1) (p i) (p d.1) := by
    rw [hqShape, hAShape]
    simp [listZeroAngleMass, hqFirstNe, hHidden, hqLastNe]

  rw [hmassEq] at hmassRot
  exact ⟨r,b,c,d,
    hrTop,hbTop,hcTop,hdTop,
    hrb,hrc,hrd,hbc,hbd,hcd,
    hmassRot⟩

#print axioms support_three_middle_hidden_small_matching

end JSP000404Research
