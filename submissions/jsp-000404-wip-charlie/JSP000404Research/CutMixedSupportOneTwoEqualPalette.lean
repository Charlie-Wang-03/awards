import JSP000404Research.CutQuotientRotation
import JSP000404Research.CutMixedSupportEqualPalette
import JSP000404Research.MixedSupportTransitionCeiling
import JSP000404Research.DeficitThreeSupportTwoHidden
import Mathlib.Tactic

/-!
# Mixed support-one / support-two equal-palette rigidity

Assume two saturation-bad minima share the same old cut palette.  Let a have
support one and b support two.

The support-one palette forces b's cut quotient shape:
* cut wrap quotient = n-2;
* every positive ordinary cut quotient is one;
* support two means exactly one positive ordinary quotient.

Thus the cut quotient multiset has exactly the two positive values 1 and n-2.

Independently, the canonical support-two decomposition supplies its unique
transition certificate H.  Global transition packing beside the sharp top and
the support-one minimum gives H.qe <= 2.  Full cut/canonical quotient
permutation transports H.qe into the cut quotient multiset.  Since n>=5 makes
n-2>=3, H.qe cannot be n-2, hence H.qe=1.

Therefore the hidden same-sign quotient at b is exactly n-2 and pays a genuine
Euclidean angle of at least (n-2)*lambda.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem cut_equal_palette_support_two_transition_qe_eq_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hcardV : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    {top a b : V}
    (hta : top ≠ a)
    (htb : top ≠ b)
    (hab : a ≠ b)
    (hTop : centreExponent (C top) t = n - 1)
    (hA : centreExponent (C a) t = n - 3)
    (hB : centreExponent (C b) t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient (C a) t) = 1)
    (hsupB :
      positiveSupport (centreQuotient (C b) t) = 2)
    (hBadA :
      CutSaturationBadAt
        hp hcap C
        (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
        hlam ht hdelta0 (by linarith : delta < 1)
        hc0 hcpi a)
    (hBadB :
      CutSaturationBadAt
        hp hcap C
        (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
        hlam ht hdelta0 (by linarith : delta < 1)
        hc0 hcpi b)
    (hactiveEq :
      active
          (cutProjectiveBandPartition
            hp hcap
            (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
            hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith)) a
        =
      active
          (cutProjectiveBandPartition
            hp hcap
            (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
            hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith)) b) :
    ∃ H : HighExponentTransitionIntervalCertificate hp t b (C b),
      H.qe = 1 := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht

  obtain ⟨first, rest, pre, post, qe, H,
      _hrays, hqe0, hqCanon, _hsign,
      hHqe, _hhiddenPos, _hhiddenOcc⟩ :=
    exists_deficit_three_support_two_hidden_sameSign
      hp hcap (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      b (C b) hB hsupB

  have hHle :
      H.qe ≤ 2 :=
    transition_qe_le_two_beside_top_and_support_one
      hp hcap hn5 hdelta0 hdeltaHalf ht hlam
      hta htb hab
      (C top) (C a) (C b)
      hTop hA hsupA H

  obtain ⟨R, x0, xs, hvalues, hwrap⟩ :=
    support_one_equal_palette_other_wrap_quotient_eq_n_sub_two
      hp hcap C hcardV hn5 htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi
      hA hB hsupA hsupB
      hBadA hBadB hactiveEq

  obtain ⟨_R2, _a2, _xs2, _hv2, _hspan2,
      hqLen, _hbLen, _hdom, hqPos,
      _hbPos, hqLe⟩ :=
    support_one_equal_palette_forces_other_ordinary_quotients_le_one
      hp hcap C hcardV hn5 htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi
      hA hB hsupA hsupB
      hBadA hBadB hactiveEq

  let qOrd := (successiveDiffsFrom x0 xs).map Nat.floor
  let qWrap := Nat.floor (x0 + t - xs.getLastD x0)

  have hwrapEq : qWrap = n - 2 := by
    simpa [qWrap] using hwrap

  have hcutDecomp :
      R.gapQuotients t = qOrd ++ [qWrap] := by
    unfold CentreCutRayCycle.gapQuotients
    rw [hvalues]
    simpa [qOrd, qWrap] using
      linearCyclicGapQuotients_cons_decompose t x0 xs

  have hHmemCanonical :
      H.qe ∈ quotientList t (C b).gaps :=
    H.qe_mem
  have hHmemCut :
      H.qe ∈ R.gapQuotients t :=
    R.canonical_quotient_mem_cut hp htpos hHmemCanonical
  rw [hcutDecomp, List.mem_append] at hHmemCut
  rcases hHmemCut with hOrd | hWrapMem
  · have hle1 : H.qe ≤ 1 := hqLe H.qe hOrd
    have hne : H.qe ≠ 0 := H.qe_ne
    refine ⟨H, ?_⟩
    omega
  · simp only [List.mem_singleton] at hWrapMem
    have hEqWrap : H.qe = n - 2 := by
      rw [hwrapEq] at hWrapMem
      exact hWrapMem
    rw [hEqWrap] at hHle
    omega

/-- Equal old palettes in the support-(1,2) branch force a hidden genuine
same-sign angle of at least (n-2)*lambda at the support-two bad minimum. -/
theorem cut_equal_palette_support_one_two_hidden_large_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hcardV : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    {top a b : V}
    (hta : top ≠ a)
    (htb : top ≠ b)
    (hab : a ≠ b)
    (hTop : centreExponent (C top) t = n - 1)
    (hA : centreExponent (C a) t = n - 3)
    (hB : centreExponent (C b) t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient (C a) t) = 1)
    (hsupB :
      positiveSupport (centreQuotient (C b) t) = 2)
    (hBadA :
      CutSaturationBadAt
        hp hcap C
        (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
        hlam ht hdelta0 (by linarith : delta < 1)
        hc0 hcpi a)
    (hBadB :
      CutSaturationBadAt
        hp hcap C
        (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
        hlam ht hdelta0 (by linarith : delta < 1)
        hc0 hcpi b)
    (hactiveEq :
      active
          (cutProjectiveBandPartition
            hp hcap
            (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
            hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith)) a
        =
      active
          (cutProjectiveBandPartition
            hp hcap
            (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
            hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith)) b) :
    ∃ x y : OtherVertex b,
      x ≠ y ∧
      (((n - 2 : ℕ) : ℝ) * lam) ≤
        EuclideanGeometry.angle (p x.1) (p b) (p y.1) := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht

  obtain ⟨H, hHone⟩ :=
    cut_equal_palette_support_two_transition_qe_eq_one
      hp hcap C hcardV hn5 hdelta0 hdeltaHalf
      ht hlam hc0 hcpi hta htb hab
      hTop hA hB hsupA hsupB
      hBadA hBadB hactiveEq

  obtain ⟨first, rest, pre, post, qe, H0,
      hrays, hqe0, hq, hsign,
      hH0qe, _hhiddenPos, _hhiddenOcc⟩ :=
    exists_deficit_three_support_two_hidden_sameSign
      hp hcap (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      b (C b) hB hsupB

  -- Every transition certificate at this support-two centre has the unique
  -- transition quotient, so H0.qe = H.qe = 1.
  have hH0le :
      H0.qe ≤ 2 :=
    transition_qe_le_two_beside_top_and_support_one
      hp hcap hn5 hdelta0 hdeltaHalf ht hlam
      hta htb hab
      (C top) (C a) (C b)
      hTop hA hsupA H0

  have hH0one : H0.qe = 1 := by
    have hH0mem :
        H0.qe ∈ quotientList t (C b).gaps :=
      H0.qe_mem
    -- Use the same cut quotient classification.
    obtain ⟨R, x0, xs, hvalues, hwrap⟩ :=
      support_one_equal_palette_other_wrap_quotient_eq_n_sub_two
        hp hcap C hcardV hn5 htpos hlam ht
        hdelta0 hdeltaHalf hc0 hcpi
        hA hB hsupA hsupB hBadA hBadB hactiveEq
    obtain ⟨_R2, _a2, _xs2, _hv2, _hspan2,
        _hqLen, _hbLen, _hdom, _hqPos,
        _hbPos, hqLe⟩ :=
      support_one_equal_palette_forces_other_ordinary_quotients_le_one
        hp hcap C hcardV hn5 htpos hlam ht
        hdelta0 hdeltaHalf hc0 hcpi
        hA hB hsupA hsupB hBadA hBadB hactiveEq
    let qOrd := (successiveDiffsFrom x0 xs).map Nat.floor
    let qWrap := Nat.floor (x0 + t - xs.getLastD x0)
    have hwrapEq : qWrap = n - 2 := by
      simpa [qWrap] using hwrap
    have hdecomp :
        R.gapQuotients t = qOrd ++ [qWrap] := by
      unfold CentreCutRayCycle.gapQuotients
      rw [hvalues]
      simpa [qOrd, qWrap] using
        linearCyclicGapQuotients_cons_decompose t x0 xs
    have hm :=
      R.canonical_quotient_mem_cut hp htpos hH0mem
    rw [hdecomp, List.mem_append] at hm
    rcases hm with hm | hm
    · have hle1 := hqLe H0.qe hm
      omega
    · simp only [List.mem_singleton] at hm
      rw [hwrapEq] at hm
      rw [hm] at hH0le
      omega

  have hqOne : qe = 1 := by
    rw [← hH0qe]
    exact hH0one

  subst qe
  have hsupportList :
      listPositiveCount (pre ++ 1 :: post) = 2 := by
    rw [← hq, ← centreQuotient_ofFn]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupB

  have hdelta1 : delta < 1 := by linarith
  have hsumFn :=
    deficit_three_support_two_sum
      (C b) (by omega : 4 ≤ n)
      hdelta0 hdelta1 ht hB hsupB
  have hsumList :
      (pre ++ 1 :: post).sum = n - 1 := by
    rw [← hq, ← centreQuotient_sum_eq_list_sum (C b) t]
    exact hsumFn

  exact deficit_three_support_two_unit_transition_hidden_angle
    hp htpos hlam b (C b)
    (by omega : 4 ≤ n)
    first rest pre post hrays hq hsign
    hsupportList hsumList

#print axioms cut_equal_palette_support_two_transition_qe_eq_one
#print axioms cut_equal_palette_support_one_two_hidden_large_angle

end JSP000404Research
