import JSP000404Research.SupportThreeNonTopGainPosition
import JSP000404Research.CyclicPositiveRayDeletionGain
import Mathlib.Tactic

/-!
# Concrete non-top deletion gain: right hidden support-three shape

In the right-hidden pinned shape

  top-rotation quotients = [qFirst,0,0,qHidden,qLast],

the cyclic predecessor of top is flanked by qHidden and qLast.  Rotate the
cycle four more positions so that this predecessor becomes first.  Its
outgoing quotient is qLast and its incoming quotient is qHidden, both
positive.

The actual canonical position of that predecessor depends only on whether
there are rays before top in the canonical list:

* if preTop is nonempty, delete its final ray;
* if preTop is empty, delete the final ray of postTop.

The generic cyclic-positive deletion bridge then gives one full exponent
unit of gain.
-/

namespace JSP000404Research

theorem support_three_right_hidden_has_nonTop_deletion_gain
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcard : Fintype.card V = 6)
    {t : ℝ}
    {s i : V}
    (hsi : s ≠ i)
    (C : CentreProjectiveCycle hp i)
    (k : ℕ)
    (preTop postTop : List (OtherVertex i))
    (r : OtherVertex i)
    (rest : List (OtherVertex i))
    (qFirst qLast qHidden : ℕ)
    (hsplitTop :
      C.rays =
        preTop ++ (⟨s,hsi⟩ : OtherVertex i) :: postTop)
    (hk : k = preTop.length)
    (hrotRays :
      C.rays.rotate k =
        (⟨s,hsi⟩ : OtherVertex i) :: r :: rest)
    (hqrot :
      (quotientList t C.gaps).rotate k =
        qFirst :: [0,0,qHidden] ++ [qLast])
    (hLast : 1 ≤ qLast)
    (hHidden : 1 ≤ qHidden)
    (ht0 : 0 ≤ t) :
    ∃ deleted : V, ∃ hir : i ≠ deleted,
      deleted ≠ s ∧
      let hother :
          Nonempty (OtherVertex (survivingCentre deleted i hir)) :=
        child_other_nonempty_of_card_ge_three
          (by rw [hcard]; omega) hir
      centreExponent C t + 1 ≤
        centreExponent (C.restrictDelete deleted hir hother) t := by
  let topRay : OtherVertex i := ⟨s,hsi⟩
  have hqTop :
      (quotientList t C.gaps).rotate preTop.length =
        qFirst :: [0,0,qHidden] ++ [qLast] := by
    simpa [hk] using hqrot

  have hrotTop :
      C.rays.rotate preTop.length =
        topRay :: r :: rest := by
    simpa [hk, topRay] using hrotRays
  have htailTop :
      postTop ++ preTop = r :: rest := by
    have hcanonical :
        C.rays.rotate preTop.length =
          topRay :: (postTop ++ preTop) := by
      rw [hsplitTop, List.rotate_append_length_eq]
      simp [topRay, List.append_assoc]
    rw [hrotTop] at hcanonical
    exact (List.cons.inj hcanonical).2
  have hrotNodup :
      (topRay :: r :: rest).Nodup := by
    rw [← hrotTop]
    simpa using C.nodup

  have hqLen :
      (quotientList t C.gaps).length = 5 := by
    rw [quotientList_length, C.gaps_length,
      centreRayList_length_eq_card_sub_one C, hcard]
    norm_num

  have hqPrev :
      ((quotientList t C.gaps).rotate preTop.length).rotate 4 =
        qLast :: [qFirst,0,0] ++ [qHidden] := by
    rw [hqTop]
    simp

  by_cases hpre : preTop = []
  · subst preTop
    have hpostLen : postTop.length = 4 := by
      have hlen :
          C.rays.length = 5 := by
        rw [centreRayList_length_eq_card_sub_one C, hcard]
        norm_num
      rw [hsplitTop] at hlen
      simp at hlen
      omega
    have hpostNe : postTop ≠ [] := by
      intro h
      rw [h] at hpostLen
      simp at hpostLen
    let delRay : OtherVertex i :=
      postTop.getLast hpostNe
    let preR : List (OtherVertex i) :=
      topRay :: postTop.dropLast
    let deleted : V := delRay.1
    have hir : i ≠ deleted := delRay.2

    have hpostDecomp :
        postTop = postTop.dropLast ++ [delRay] := by
      dsimp [delRay]
      exact List.dropLast_append_getLast hpostNe

    have hsplitR :
        C.rays =
          preR ++ deletedParentRay deleted i hir :: [] := by
      dsimp [preR]
      rw [hsplitTop, hpostDecomp]
      simp [topRay, deletedParentRay, deleted, hir,
        List.append_assoc]

    have hpreRLen : preR.length = 4 := by
      dsimp [preR]
      have hdrop :
          postTop.dropLast.length = 3 := by
        rw [List.length_dropLast, hpostLen]
        norm_num
      simp [hdrop]

    have hqTarget :
        (quotientList t C.gaps).rotate preR.length =
          qLast :: [qFirst,0,0] ++ [qHidden] := by
      rw [hpreRLen]
      simpa using hqPrev

    have hdelTop : deleted ≠ s := by
      intro hds
      have hEq : delRay = topRay := by
        apply Subtype.ext
        exact hds
      have htopNotTail :
          topRay ∉ r :: rest :=
        (List.nodup_cons.mp hrotNodup).1
      have hdelTail :
          delRay ∈ r :: rest := by
        rw [← htailTop, hpostDecomp]
        simp
      exact htopNotTail (by simpa [hEq] using hdelTail)

    let hother :
        Nonempty (OtherVertex (survivingCentre deleted i hir)) :=
      child_other_nonempty_of_card_ge_three
        (by rw [hcard]; omega) hir

    have hgain :=
      centreExponent_gain_delete_of_rotated_positive_ends
        C hir hother preR [] hsplitR ht0
        qLast qHidden [qFirst,0,0]
        hqTarget hLast hHidden
    exact ⟨deleted, hir, hdelTop, by
      simpa [hir, hother] using hgain⟩

  · let delRay : OtherVertex i :=
      preTop.getLast hpre
    let preR : List (OtherVertex i) :=
      preTop.dropLast
    let deleted : V := delRay.1
    have hir : i ≠ deleted := delRay.2

    have hpreDecomp :
        preTop = preR ++ [delRay] := by
      dsimp [preR, delRay]
      exact List.dropLast_append_getLast hpre

    have hsplitR :
        C.rays =
          preR ++
            deletedParentRay deleted i hir ::
              (topRay :: postTop) := by
      rw [hsplitTop, hpreDecomp]
      simp [topRay, deletedParentRay, deleted, hir,
        List.append_assoc]

    have hpreLenSucc :
        preR.length + 1 = preTop.length := by
      rw [hpreDecomp]
      simp

    have hqTargetShift :
        ((quotientList t C.gaps).rotate preR.length).rotate 1 =
          (quotientList t C.gaps).rotate preTop.length := by
      rw [List.rotate_rotate, hpreLenSucc]

    have hqTarget :
        (quotientList t C.gaps).rotate preR.length =
          qLast :: [qFirst,0,0] ++ [qHidden] := by
      let qs := quotientList t C.gaps
      have hcandidate :
          (qLast :: [qFirst,0,0] ++ [qHidden]).rotate 1 =
            qFirst :: [0,0,qHidden] ++ [qLast] := by
        simp
      have hrot1 :
          ((qs.rotate preR.length).rotate 1) =
            (qLast :: [qFirst,0,0] ++ [qHidden]).rotate 1 := by
        rw [hqTargetShift, hqTop, hcandidate]
      have hrot4 :=
        congrArg (fun l : List ℕ => l.rotate 4) hrot1
      have hleft :
          ((qs.rotate preR.length).rotate 1).rotate 4 =
            qs.rotate preR.length := by
        rw [List.rotate_rotate, List.rotate_rotate]
        have hlen :
            (qs.rotate preR.length).length = 5 := by
          rw [List.length_rotate, hqLen]
        simpa [hlen]
      have hright :
          ((qLast :: [qFirst,0,0] ++ [qHidden]).rotate 1).rotate 4 =
            qLast :: [qFirst,0,0] ++ [qHidden] := by
        simp
      rw [hleft, hright] at hrot4
      exact hrot4

    have hdelTop : deleted ≠ s := by
      intro hds
      have hEq : delRay = topRay := by
        apply Subtype.ext
        exact hds
      have htopNotTail :
          topRay ∉ r :: rest :=
        (List.nodup_cons.mp hrotNodup).1
      have hdelTail :
          delRay ∈ r :: rest := by
        rw [← htailTop, hpreDecomp]
        simp
      exact htopNotTail (by simpa [hEq] using hdelTail)

    let hother :
        Nonempty (OtherVertex (survivingCentre deleted i hir)) :=
      child_other_nonempty_of_card_ge_three
        (by rw [hcard]; omega) hir

    have hgain :=
      centreExponent_gain_delete_of_rotated_positive_ends
        C hir hother preR (topRay :: postTop)
        hsplitR ht0 qLast qHidden [qFirst,0,0]
        hqTarget hLast hHidden
    exact ⟨deleted, hdelTop, hir.symm, by
      simpa [hir, hother] using hgain⟩

#print axioms support_three_right_hidden_has_nonTop_deletion_gain

end JSP000404Research
