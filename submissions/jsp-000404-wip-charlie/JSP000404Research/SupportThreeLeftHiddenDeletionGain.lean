import JSP000404Research.SupportThreeNonTopGainPosition
import JSP000404Research.CyclicPositiveRayDeletionGain
import Mathlib.Tactic

/-!
# Concrete non-top deletion gain: left hidden support-three shape

Pin a six-point support-three centre at the sharp top.  In the left-hidden
shape

  rotated rays      = top :: r :: rest,
  rotated quotients = qFirst :: [qHidden,0,0] ++ [qLast],

the non-top ray r is flanked by qFirst and qHidden.

Rotate one further step.  The ray r moves to the front and its outgoing /
incoming cyclic quotients become qHidden and qFirst, both positive.  The
position-free cyclic deletion bridge then shows that deleting the vertex r
raises this support-three centre exponent by at least one.
-/

namespace JSP000404Research

theorem support_three_left_hidden_nonTop_deletion_gain
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ}
    {s i : V}
    (hsi : s ≠ i)
    (C : CentreProjectiveCycle hp i)
    (first0 : OtherVertex i)
    (rest0 : List (OtherVertex i))
    (k : ℕ)
    (preTop postTop : List (OtherVertex i))
    (r : OtherVertex i)
    (rest : List (OtherVertex i))
    (qFirst qLast qHidden : ℕ)
    (hrays0 : C.rays = first0 :: rest0)
    (hsplitTop :
      C.rays =
        preTop ++ (⟨s,hsi⟩ : OtherVertex i) :: postTop)
    (hk : k = preTop.length)
    (hrotRays :
      C.rays.rotate k =
        (⟨s,hsi⟩ : OtherVertex i) :: r :: rest)
    (hqrot :
      (quotientList t C.gaps).rotate k =
        qFirst :: [qHidden,0,0] ++ [qLast])
    (hFirst : 1 ≤ qFirst)
    (hHidden : 1 ≤ qHidden)
    (ht0 : 0 ≤ t) :
    let deleted := r.1
    let hir : i ≠ deleted := r.2
    let hother :
        Nonempty (OtherVertex (survivingCentre deleted i hir)) := by
      have hcardR :
          C.rays.length = Fintype.card V - 1 :=
        centreRayList_length_eq_card_sub_one C
      have hcardV : 2 ≤ Fintype.card V := by
        by_contra h
        have hc : Fintype.card V ≤ 1 := by omega
        rw [hcardR] at hrays0
        have hlen : C.rays.length = 0 := by omega
        exact C.nonempty (List.length_eq_zero.mp hlen)
      exact child_other_nonempty_of_card_ge_three
        (by
          have hlenRot :
              C.rays.length = 5 := by
            rw [← List.length_rotate C.rays k, hrotRays]
            simp at *
          rw [centreRayList_length_eq_card_sub_one C] at hlenRot
          omega)
        hir
    centreExponent C t + 1 ≤
      centreExponent (C.restrictDelete deleted hir hother) t := by
  let topRay : OtherVertex i := ⟨s,hsi⟩
  let deleted := r.1
  let hir : i ≠ deleted := r.2

  have hrotTop :
      C.rays.rotate preTop.length =
        topRay :: r :: rest := by
    simpa [topRay, hk] using hrotRays
  have htailTop :
      postTop ++ preTop = r :: rest := by
    have hcanonical :
        C.rays.rotate preTop.length =
          topRay :: (postTop ++ preTop) := by
      rw [hsplitTop, List.rotate_append_length_eq]
      simp [topRay, List.append_assoc]
    rw [hrotTop] at hcanonical
    exact (List.cons.inj hcanonical).2

  have hqTop :
      (quotientList t C.gaps).rotate preTop.length =
        qFirst :: [qHidden,0,0] ++ [qLast] := by
    simpa [hk] using hqrot

  have hqTarget :
      (quotientList t C.gaps).rotate (preTop.length + 1) =
        qHidden :: [0,0,qLast] ++ [qFirst] := by
    calc
      (quotientList t C.gaps).rotate (preTop.length + 1)
          =
        ((quotientList t C.gaps).rotate preTop.length).rotate 1 := by
            rw [List.rotate_rotate]
      _ = (qFirst :: [qHidden,0,0] ++ [qLast]).rotate 1 := by
            rw [hqTop]
      _ = qHidden :: [0,0,qLast] ++ [qFirst] := by
            simp

  have hcardRays : C.rays.length = 5 := by
    rw [← List.length_rotate C.rays preTop.length, hrotTop]
    simp at *
    have hqLen :
        (quotientList t C.gaps).length = C.rays.length := by
      rw [quotientList_length, C.gaps_length]
    have hqLenRot :
        ((quotientList t C.gaps).rotate preTop.length).length =
          (qFirst :: [qHidden,0,0] ++ [qLast]).length := by
      rw [hqTop]
    rw [List.length_rotate, hqLen] at hqLenRot
    simpa using hqLenRot

  let hcardV3 : 3 ≤ Fintype.card V := by
    rw [centreRayList_length_eq_card_sub_one C] at hcardRays
    omega
  let hother :
      Nonempty (OtherVertex (survivingCentre deleted i hir)) :=
    child_other_nonempty_of_card_ge_three hcardV3 hir

  cases hpost : postTop with
  | nil =>
      have hpre :
          preTop = r :: rest := by
        simpa [hpost] using htailTop
      have hsplitR :
          C.rays =
            [] ++
              deletedParentRay deleted i hir ::
                (rest ++ [topRay]) := by
        rw [hsplitTop, hpost, hpre]
        simp [topRay, deletedParentRay, deleted, hir,
          List.append_assoc]
      have hrotLen :
          preTop.length + 1 = C.rays.length := by
        rw [hpre, hcardRays]
        have hrestLen :
            rest.length = 3 := by
          have hlen := congrArg List.length hrotTop
          rw [List.length_rotate, hcardRays] at hlen
          simp at hlen
          omega
        simp [hpre, hrestLen]
      have hqTarget0 :
          (quotientList t C.gaps).rotate 0 =
            qHidden :: [0,0,qLast] ++ [qFirst] := by
        have hperiod :
            (quotientList t C.gaps).rotate (preTop.length + 1) =
              (quotientList t C.gaps).rotate 0 := by
          rw [hrotLen]
          simp
        rw [← hperiod]
        exact hqTarget
      exact centreExponent_gain_delete_of_rotated_positive_ends
        C hir hother [] (rest ++ [topRay])
        hsplitR ht0 qHidden qFirst [0,0,qLast]
        hqTarget0 hHidden hFirst

  | cons next postTail =>
      have hhead :
          next = r := by
        have h :=
          congrArg List.head? htailTop
        rw [hpost] at h
        simp at h
        exact h
      subst next
      have htail :
          postTail ++ preTop = rest := by
        rw [hpost] at htailTop
        simp only [List.cons_append] at htailTop
        exact (List.cons.inj htailTop).2
      let preR := preTop ++ [topRay]
      have hsplitR :
          C.rays =
            preR ++ deletedParentRay deleted i hir :: postTail := by
        dsimp [preR]
        rw [hsplitTop, hpost]
        simp [topRay, deletedParentRay, deleted, hir,
          List.append_assoc]
      have hpreRLen :
          preR.length = preTop.length + 1 := by
        simp [preR]
      have hqTargetR :
          (quotientList t C.gaps).rotate preR.length =
            qHidden :: [0,0,qLast] ++ [qFirst] := by
        rw [hpreRLen]
        exact hqTarget
      exact centreExponent_gain_delete_of_rotated_positive_ends
        C hir hother preR postTail
        hsplitR ht0 qHidden qFirst [0,0,qLast]
        hqTargetR hHidden hFirst

#print axioms support_three_left_hidden_nonTop_deletion_gain

end JSP000404Research
