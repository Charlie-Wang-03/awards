import JSP000404Research.SupportThreePinnedMiddleShape
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Explicit five-ray cycle certificate for the middle-hidden terminal

`SupportThreePinnedMiddleShape` stores the middle-hidden quotient pattern but
leaves the three rays following the top ray packed into an anonymous list.

In a six-point configuration every centre has exactly five projective rays.
Hence the pinned cycle can be unpacked canonically as

  rays.rotate k = [top, r, b, c, d]
  quotients.rotate k = [qFirst, 0, qHidden, 0, qLast].

This certificate also retains the original canonical split

  rays = preTop ++ [top] ++ postTop

and therefore the exact location of the canonical projective wrap after the
rotation:

  postTop ++ preTop = [r,b,c,d].

That last identity is the bookkeeping datum needed to translate the lifted
three-transition sign pattern back to the raw canonical Boolean signs.
-/

namespace JSP000404Research

structure MiddleHiddenPinnedCycleCertificate
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (top i : V)
    (htopi : top ≠ i)
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) where
  k : ℕ
  preTop : List (OtherVertex i)
  postTop : List (OtherVertex i)
  r : OtherVertex i
  b : OtherVertex i
  c : OtherVertex i
  d : OtherVertex i
  qFirst : ℕ
  qHidden : ℕ
  qLast : ℕ
  rays_split :
    C.rays =
      preTop ++ (⟨top, htopi⟩ : OtherVertex i) :: postTop
  k_eq : k = preTop.length
  rays_rotate :
    C.rays.rotate k =
      (⟨top, htopi⟩ : OtherVertex i) :: r :: b :: c :: d :: []
  quotients_rotate :
    (quotientList t C.gaps).rotate k =
      qFirst :: 0 :: qHidden :: 0 :: qLast :: []
  qFirst_pos : 1 ≤ qFirst
  qHidden_ne : qHidden ≠ 0
  qLast_pos : 1 ≤ qLast
  tail_split :
    postTop ++ preTop = r :: b :: c :: d :: []

namespace MiddleHiddenPinnedCycleCertificate

theorem ray_length_eq_five
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {hp : Function.Injective p}
    {top i : V} {htopi : top ≠ i}
    {C : CentreProjectiveCycle hp i} {t : ℝ}
    (H : MiddleHiddenPinnedCycleCertificate hp top i htopi C t) :
    C.rays.length = 5 := by
  have h := congrArg List.length H.rays_rotate
  rw [List.length_rotate] at h
  simpa using h

theorem quotient_length_eq_five
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {hp : Function.Injective p}
    {top i : V} {htopi : top ≠ i}
    {C : CentreProjectiveCycle hp i} {t : ℝ}
    (H : MiddleHiddenPinnedCycleCertificate hp top i htopi C t) :
    (quotientList t C.gaps).length = 5 := by
  rw [quotientList_length, C.gaps_length]
  exact H.ray_length_eq_five

theorem pre_post_length_eq_four
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {hp : Function.Injective p}
    {top i : V} {htopi : top ≠ i}
    {C : CentreProjectiveCycle hp i} {t : ℝ}
    (H : MiddleHiddenPinnedCycleCertificate hp top i htopi C t) :
    H.postTop.length + H.preTop.length = 4 := by
  have hlen := congrArg List.length H.tail_split
  simpa using hlen

theorem preTop_length_le_four
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {hp : Function.Injective p}
    {top i : V} {htopi : top ≠ i}
    {C : CentreProjectiveCycle hp i} {t : ℝ}
    (H : MiddleHiddenPinnedCycleCertificate hp top i htopi C t) :
    H.preTop.length ≤ 4 := by
  have h := H.pre_post_length_eq_four
  omega

theorem postTop_length_le_four
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {hp : Function.Injective p}
    {top i : V} {htopi : top ≠ i}
    {C : CentreProjectiveCycle hp i} {t : ℝ}
    (H : MiddleHiddenPinnedCycleCertificate hp top i htopi C t) :
    H.postTop.length ≤ 4 := by
  have h := H.pre_post_length_eq_four
  omega

end MiddleHiddenPinnedCycleCertificate

theorem exists_middle_hidden_pinned_cycle_certificate
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {t : ℝ}
    {top i : V}
    (hp : Function.Injective p)
    (hcard : Fintype.card V = 6)
    (htopi : top ≠ i)
    (C : CentreProjectiveCycle hp i)
    (hmiddle :
      SupportThreePinnedMiddleShape hp htopi C) :
    Nonempty
      (MiddleHiddenPinnedCycleCertificate
        hp top i htopi C t) := by
  classical
  obtain ⟨_first0, _rest0, k, preTop, postTop,
      r, rest, qFirst, qLast, qHidden,
      _hrays0, hsplit, hk, hrot, hqrot,
      hFirst, hLast, hHidden⟩ := hmiddle

  have hlenRays : C.rays.length = 5 := by
    rw [centreRayList_length_eq_card_sub_one C, hcard]
    norm_num
  have hlenRot : (C.rays.rotate k).length = 5 := by
    rw [List.length_rotate, hlenRays]
  rw [hrot] at hlenRot
  simp only [List.length_cons] at hlenRot
  have hrestLen : rest.length = 3 := by
    omega

  obtain ⟨b,c,d,hrest⟩ :
      ∃ b c d : OtherVertex i, rest = [b,c,d] := by
    cases rest with
    | nil =>
        simp at hrestLen
    | cons b rest1 =>
        cases rest1 with
        | nil =>
            simp at hrestLen
        | cons c rest2 =>
            cases rest2 with
            | nil =>
                simp at hrestLen
            | cons d rest3 =>
                have hnil : rest3 = [] := by
                  simpa using hrestLen
                subst rest3
                exact ⟨b,c,d,rfl⟩

  let topRay : OtherVertex i := ⟨top, htopi⟩

  have hrotShape :
      C.rays.rotate k =
        topRay :: r :: b :: c :: d :: [] := by
    simpa [topRay, hrest] using hrot

  have hqShape :
      (quotientList t C.gaps).rotate k =
        qFirst :: 0 :: qHidden :: 0 :: qLast :: [] := by
    simpa [List.append_assoc] using hqrot

  have hrotCanonical :
      C.rays.rotate preTop.length =
        topRay :: (postTop ++ preTop) := by
    rw [hsplit, List.rotate_append_length_eq]
    simp [topRay, List.append_assoc]

  have hrotDisplayed :
      C.rays.rotate preTop.length =
        topRay :: r :: b :: c :: d :: [] := by
    rw [← hk]
    exact hrotShape

  have htail :
      postTop ++ preTop = r :: b :: c :: d :: [] := by
    rw [hrotDisplayed] at hrotCanonical
    exact (List.cons.inj hrotCanonical).2

  exact ⟨{
    k := k
    preTop := preTop
    postTop := postTop
    r := r
    b := b
    c := c
    d := d
    qFirst := qFirst
    qHidden := qHidden
    qLast := qLast
    rays_split := hsplit
    k_eq := hk
    rays_rotate := hrotShape
    quotients_rotate := hqShape
    qFirst_pos := hFirst
    qHidden_ne := hHidden
    qLast_pos := hLast
    tail_split := htail
  }⟩

#print axioms MiddleHiddenPinnedCycleCertificate.ray_length_eq_five
#print axioms MiddleHiddenPinnedCycleCertificate.quotient_length_eq_five
#print axioms MiddleHiddenPinnedCycleCertificate.pre_post_length_eq_four
#print axioms exists_middle_hidden_pinned_cycle_certificate

end JSP000404Research
