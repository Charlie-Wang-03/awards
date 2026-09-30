import JSP000404Research.SupportThreeMiddleHiddenWrapCases
import JSP000404Research.SupportThreeMiddleHiddenRawSignCases
import JSP000404Research.NonExposedSupportThreeExactTransitions
import Mathlib.Tactic

/-!
# Canonical raw sign classification for a non-exposed middle-hidden centre

A non-exposed support-three centre changes sign exactly on its three positive
quotient positions.  The explicit middle-hidden cycle certificate retains the
old canonical projective wrap, so the five pure Boolean wrap lemmas can now be
applied to the actual canonical ray signs.

The result is a five-case certificate.  Each case records both the canonical
wrap position and the resulting raw sign pattern relative to the ray pointing
to the distinguished top vertex.
-/

namespace JSP000404Research

theorem nonexposed_middle_hidden_canonical_sign_cases
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (htone : 1 ≤ t)
    (hlam : lam = Real.pi / t)
    (hcard : Fintype.card V = 6)
    {top i : V}
    (htopi : top ≠ i)
    (C : CentreProjectiveCycle hp i)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3)
    (hnot : ¬ StrictlyExposedAt p i)
    (hmiddle :
      SupportThreePinnedMiddleShape hp htopi C) :
    ∃ H : MiddleHiddenPinnedCycleCertificate hp top i htopi C t,
      let sTop :=
        raySignAt hp i
          (⟨top, htopi⟩ : OtherVertex i)
      let sr := raySignAt hp i H.r
      let sb := raySignAt hp i H.b
      let sc := raySignAt hp i H.c
      let sd := raySignAt hp i H.d
      (
        (H.postTop = [] ∧
          H.preTop = [H.r,H.b,H.c,H.d] ∧
          sr = sTop ∧ sb = sTop ∧
          sc = !sTop ∧ sd = !sTop)
        ∨
        (H.postTop = [H.r] ∧
          H.preTop = [H.b,H.c,H.d] ∧
          sr = !sTop ∧ sb = sTop ∧
          sc = !sTop ∧ sd = !sTop)
        ∨
        (H.postTop = [H.r,H.b] ∧
          H.preTop = [H.c,H.d] ∧
          sr = !sTop ∧ sb = !sTop ∧
          sc = !sTop ∧ sd = !sTop)
        ∨
        (H.postTop = [H.r,H.b,H.c] ∧
          H.preTop = [H.d] ∧
          sr = !sTop ∧ sb = !sTop ∧
          sc = sTop ∧ sd = !sTop)
        ∨
        (H.postTop = [H.r,H.b,H.c,H.d] ∧
          H.preTop = [] ∧
          sr = !sTop ∧ sb = !sTop ∧
          sc = sTop ∧ sd = sTop)
      ) := by
  classical
  let H :=
    Classical.choice
      (exists_middle_hidden_pinned_cycle_certificate
        hp hcard htopi C hmiddle)
  let topRay : OtherVertex i := ⟨top, htopi⟩
  let sTop := raySignAt hp i topRay
  let sr := raySignAt hp i H.r
  let sb := raySignAt hp i H.b
  let sc := raySignAt hp i H.c
  let sd := raySignAt hp i H.d

  obtain ⟨first, rest, hrays, hexact⟩ :=
    nonexposed_support_three_changes_exactly_on_positive
      hp hcap ht htone hlam i C hsupport hnot

  have hFirstNe : H.qFirst ≠ 0 := by
    omega
  have hLastNe : H.qLast ≠ 0 := by
    omega
  have hqLen :
      (quotientList t C.gaps).length = 5 :=
    H.quotient_length_eq_five

  refine ⟨H, ?_⟩
  dsimp only
  rcases H.canonical_wrap_cases with h0 | h1 | h2 | h3 | h4

  · left
    have hcanon :
        C.rays =
          H.r :: H.b :: H.c :: H.d :: topRay :: [] := by
      rw [H.rays_split, h0.1, h0.2]
      simp [topRay, List.append_assoc]
    have hfr :
        first :: rest =
          H.r :: H.b :: H.c :: H.d :: topRay :: [] :=
      hrays.symm.trans hcanon
    have hf : first = H.r := (List.cons.inj hfr).1
    have hrestEq :
        rest = [H.b,H.c,H.d,topRay] :=
      (List.cons.inj hfr).2

    have hk : H.k = 4 := by
      rw [H.k_eq, h0.2]
      rfl
    have hqrot :
        (quotientList t C.gaps).rotate 4 =
          [H.qFirst,0,H.qHidden,0,H.qLast] := by
      simpa [hk] using H.quotients_rotate
    have hqcanon :=
      eq_rotate_one_of_rotate_four_eq
        (quotientList t C.gaps)
        [H.qFirst,0,H.qHidden,0,H.qLast]
        hqLen hqrot
    have hqcanon' :
        quotientList t C.gaps =
          [0,H.qHidden,0,H.qLast,H.qFirst] := by
      simpa using hqcanon

    have hexact' :
        ChangesExactlyOnPositive
          sr [sb,sc,sd,sTop,!sr]
          [0,H.qHidden,0,H.qLast,H.qFirst] := by
      rw [hf, hrestEq, hqcanon'] at hexact
      simpa [liftedCentreSignPath, sr, sb, sc, sd,
        sTop, topRay] using hexact
    have hs :=
      middle_hidden_raw_sign_shape_wrap0
        sTop sr sb sc sd
        H.qFirst H.qHidden H.qLast
        hFirstNe H.qHidden_ne hLastNe hexact'
    exact ⟨h0.1,h0.2,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2⟩

  · right; left
    have hcanon :
        C.rays =
          H.b :: H.c :: H.d :: topRay :: H.r :: [] := by
      rw [H.rays_split, h1.1, h1.2]
      simp [topRay, List.append_assoc]
    have hfr :
        first :: rest =
          H.b :: H.c :: H.d :: topRay :: H.r :: [] :=
      hrays.symm.trans hcanon
    have hf : first = H.b := (List.cons.inj hfr).1
    have hrestEq :
        rest = [H.c,H.d,topRay,H.r] :=
      (List.cons.inj hfr).2

    have hk : H.k = 3 := by
      rw [H.k_eq, h1.2]
      rfl
    have hqrot :
        (quotientList t C.gaps).rotate 3 =
          [H.qFirst,0,H.qHidden,0,H.qLast] := by
      simpa [hk] using H.quotients_rotate
    have hqcanon :=
      eq_rotate_two_of_rotate_three_eq
        (quotientList t C.gaps)
        [H.qFirst,0,H.qHidden,0,H.qLast]
        hqLen hqrot
    have hqcanon' :
        quotientList t C.gaps =
          [H.qHidden,0,H.qLast,H.qFirst,0] := by
      simpa using hqcanon

    have hexact' :
        ChangesExactlyOnPositive
          sb [sc,sd,sTop,sr,!sb]
          [H.qHidden,0,H.qLast,H.qFirst,0] := by
      rw [hf, hrestEq, hqcanon'] at hexact
      simpa [liftedCentreSignPath, sr, sb, sc, sd,
        sTop, topRay] using hexact
    have hs :=
      middle_hidden_raw_sign_shape_wrap1
        sTop sr sb sc sd
        H.qFirst H.qHidden H.qLast
        hFirstNe H.qHidden_ne hLastNe hexact'
    exact ⟨h1.1,h1.2,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2⟩

  · right; right; left
    have hcanon :
        C.rays =
          H.c :: H.d :: topRay :: H.r :: H.b :: [] := by
      rw [H.rays_split, h2.1, h2.2]
      simp [topRay, List.append_assoc]
    have hfr :
        first :: rest =
          H.c :: H.d :: topRay :: H.r :: H.b :: [] :=
      hrays.symm.trans hcanon
    have hf : first = H.c := (List.cons.inj hfr).1
    have hrestEq :
        rest = [H.d,topRay,H.r,H.b] :=
      (List.cons.inj hfr).2

    have hk : H.k = 2 := by
      rw [H.k_eq, h2.2]
      rfl
    have hqrot :
        (quotientList t C.gaps).rotate 2 =
          [H.qFirst,0,H.qHidden,0,H.qLast] := by
      simpa [hk] using H.quotients_rotate
    have hqcanon :=
      eq_rotate_three_of_rotate_two_eq
        (quotientList t C.gaps)
        [H.qFirst,0,H.qHidden,0,H.qLast]
        hqLen hqrot
    have hqcanon' :
        quotientList t C.gaps =
          [0,H.qLast,H.qFirst,0,H.qHidden] := by
      simpa using hqcanon

    have hexact' :
        ChangesExactlyOnPositive
          sc [sd,sTop,sr,sb,!sc]
          [0,H.qLast,H.qFirst,0,H.qHidden] := by
      rw [hf, hrestEq, hqcanon'] at hexact
      simpa [liftedCentreSignPath, sr, sb, sc, sd,
        sTop, topRay] using hexact
    have hs :=
      middle_hidden_raw_sign_shape_wrap2
        sTop sr sb sc sd
        H.qFirst H.qHidden H.qLast
        hFirstNe H.qHidden_ne hLastNe hexact'
    exact ⟨h2.1,h2.2,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2⟩

  · right; right; right; left
    have hcanon :
        C.rays =
          H.d :: topRay :: H.r :: H.b :: H.c :: [] := by
      rw [H.rays_split, h3.1, h3.2]
      simp [topRay, List.append_assoc]
    have hfr :
        first :: rest =
          H.d :: topRay :: H.r :: H.b :: H.c :: [] :=
      hrays.symm.trans hcanon
    have hf : first = H.d := (List.cons.inj hfr).1
    have hrestEq :
        rest = [topRay,H.r,H.b,H.c] :=
      (List.cons.inj hfr).2

    have hk : H.k = 1 := by
      rw [H.k_eq, h3.2]
      rfl
    have hqrot :
        (quotientList t C.gaps).rotate 1 =
          [H.qFirst,0,H.qHidden,0,H.qLast] := by
      simpa [hk] using H.quotients_rotate
    have hqcanon :=
      eq_rotate_four_of_rotate_one_eq
        (quotientList t C.gaps)
        [H.qFirst,0,H.qHidden,0,H.qLast]
        hqLen hqrot
    have hqcanon' :
        quotientList t C.gaps =
          [H.qLast,H.qFirst,0,H.qHidden,0] := by
      simpa using hqcanon

    have hexact' :
        ChangesExactlyOnPositive
          sd [sTop,sr,sb,sc,!sd]
          [H.qLast,H.qFirst,0,H.qHidden,0] := by
      rw [hf, hrestEq, hqcanon'] at hexact
      simpa [liftedCentreSignPath, sr, sb, sc, sd,
        sTop, topRay] using hexact
    have hs :=
      middle_hidden_raw_sign_shape_wrap3
        sTop sr sb sc sd
        H.qFirst H.qHidden H.qLast
        hFirstNe H.qHidden_ne hLastNe hexact'
    exact ⟨h3.1,h3.2,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2⟩

  · right; right; right; right
    have hcanon :
        C.rays =
          topRay :: H.r :: H.b :: H.c :: H.d :: [] := by
      rw [H.rays_split, h4.1, h4.2]
      simp [topRay, List.append_assoc]
    have hfr :
        first :: rest =
          topRay :: H.r :: H.b :: H.c :: H.d :: [] :=
      hrays.symm.trans hcanon
    have hf : first = topRay := (List.cons.inj hfr).1
    have hrestEq :
        rest = [H.r,H.b,H.c,H.d] :=
      (List.cons.inj hfr).2

    have hk : H.k = 0 := by
      rw [H.k_eq, h4.2]
      rfl
    have hqcanon' :
        quotientList t C.gaps =
          [H.qFirst,0,H.qHidden,0,H.qLast] := by
      have hq := H.quotients_rotate
      simpa [hk] using hq

    have hexact' :
        ChangesExactlyOnPositive
          sTop [sr,sb,sc,sd,!sTop]
          [H.qFirst,0,H.qHidden,0,H.qLast] := by
      rw [hf, hrestEq, hqcanon'] at hexact
      simpa [liftedCentreSignPath, sr, sb, sc, sd,
        sTop, topRay] using hexact
    have hs :=
      middle_hidden_raw_sign_shape_wrap4
        sTop sr sb sc sd
        H.qFirst H.qHidden H.qLast
        hFirstNe H.qHidden_ne hLastNe hexact'
    exact ⟨h4.1,h4.2,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2⟩

#print axioms nonexposed_middle_hidden_canonical_sign_cases

end JSP000404Research
