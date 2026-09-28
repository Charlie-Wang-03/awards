import JSP000404Research.CutSpanNMinusOneQuotientShape
import JSP000404Research.MixedSupportTransitionCeiling
import JSP000404Research.DeficitThreeSupportTwoHidden
import JSP000404Research.CutQuotientRotation
import Mathlib.Tactic

/-!
# Support-(1,2) boundary-swap quotient rigidity

Let top be the sharp n-1 centre, a a support-one n-3 minimum, and b a
support-two n-3 saturation-bad minimum.

Assume the cut-sorted floor span at b is n-1.  The exact saturated seam
arithmetic gives

  qWrap = 2,

while the ordinary quotient list has positive support one and sum n-3.

The canonical support-two transition certificate at b has quotient at most two
by global transition packing beside top and a.  Cut/canonical quotient
invariance puts its quotient into the cut quotient multiset.  The only positive
cut values are 2 and n-3, so the transition quotient is exactly 2.

The other support-two positive quotient is therefore n-3 and is same-sign,
hence pays a genuine Euclidean angle at least (n-3)*lambda.
-/

namespace JSP000404Research

theorem cut_span_n_sub_one_support_two_transition_qe_eq_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
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
    (hsupA :
      positiveSupport (centreQuotient (C a) t) = 1)
    (hB : centreExponent (C b) t = n - 3)
    (hsupB :
      positiveSupport (centreQuotient (C b) t) = 2)
    (hBadB :
      CutSaturationBadAt
        hp hcap C
        (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
        hlam ht hdelta0 (by linarith : delta < 1)
        hc0 hcpi b)
    (R : CentreCutRayCycle hp (C b) c)
    {x0 : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = x0 :: xs)
    (hspan :
      Nat.floor (xs.getLastD x0) - Nat.floor x0 = n - 1) :
    ∃ H : HighExponentTransitionIntervalCertificate hp t b (C b),
      H.qe = 2 := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht

  obtain ⟨first, rest, pre, post, qe, H,
      _hrays, hqe0, _hqCanon, _hsign,
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

  obtain ⟨hwrap, hqOrdSum, hqOrdPos⟩ :=
    cutSaturationBadAt_span_n_sub_one_support_two_shape
      hp hcap C hn5 htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi
      b hB hsupB hBadB R hvalues hspan

  let qOrd :=
    (successiveDiffsFrom x0 xs).map Nat.floor
  let qWrap :=
    Nat.floor (x0 + t - xs.getLastD x0)

  have hshapeFull :=
    cutSaturationBadAt_span_n_sub_one_quotient_shape
      hp hcap C hn5 htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi
      b hB hsupB hBadB R hvalues hspan
  have hdecomp :
      R.gapQuotients t = qOrd ++ [qWrap] := by
    simpa [qOrd, qWrap] using hshapeFull.2.2.2
  have hqWrap : qWrap = 2 := by
    simpa [qWrap] using hwrap
  have hqOrdSum' : qOrd.sum = n - 3 := by
    simpa [qOrd] using hqOrdSum
  have hqOrdPos' : listPositiveCount qOrd = 1 := by
    simpa [qOrd] using hqOrdPos

  have hHmemCanonical :
      H.qe ∈ quotientList t (C b).gaps :=
    H.qe_mem
  have hHmemCut :
      H.qe ∈ R.gapQuotients t :=
    R.canonical_quotient_mem_cut hp htpos hHmemCanonical
  rw [hdecomp, List.mem_append] at hHmemCut
  rcases hHmemCut with hOrd | hWrap
  · have hHpos : H.qe ≠ 0 := H.qe_ne
    have hsumEq :
        qOrd.sum = H.qe :=
      list_sum_eq_member_of_positiveCount_one
        qOrd hqOrdPos' hOrd hHpos
    rw [hqOrdSum'] at hsumEq
    refine ⟨H, ?_⟩
    omega
  · simp only [List.mem_singleton] at hWrap
    rw [hqWrap] at hWrap
    exact ⟨H, hWrap⟩

/-- The same branch carries a genuine same-sign angle of size at least
(n-3)*lambda. -/
theorem cut_span_n_sub_one_support_two_hidden_angle_ge_n_sub_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
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
    (hsupA :
      positiveSupport (centreQuotient (C a) t) = 1)
    (hB : centreExponent (C b) t = n - 3)
    (hsupB :
      positiveSupport (centreQuotient (C b) t) = 2)
    (hBadB :
      CutSaturationBadAt
        hp hcap C
        (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht)
        hlam ht hdelta0 (by linarith : delta < 1)
        hc0 hcpi b)
    (R : CentreCutRayCycle hp (C b) c)
    {x0 : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = x0 :: xs)
    (hspan :
      Nat.floor (xs.getLastD x0) - Nat.floor x0 = n - 1) :
    ∃ x y : OtherVertex b,
      x ≠ y ∧
      (((n - 3 : ℕ) : ℝ) * lam) ≤
        EuclideanGeometry.angle (p x.1) (p b) (p y.1) := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht

  obtain ⟨first, rest, pre, post, qe, H,
      hrays, hqe0, hqCanon, hsign,
      hHqe, _hhiddenPos, hhiddenOcc⟩ :=
    exists_deficit_three_support_two_hidden_sameSign
      hp hcap (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      b (C b) hB hsupB

  have hqe : qe = 2 := by
    rw [← hHqe]
    have hle :=
      transition_qe_le_two_beside_top_and_support_one
        hp hcap hn5 hdelta0 hdeltaHalf ht hlam
        hta htb hab
        (C top) (C a) (C b)
        hTop hA hsupA H
    have hmemCanonical : H.qe ∈ quotientList t (C b).gaps := H.qe_mem
    have hmemCut :
        H.qe ∈ R.gapQuotients t :=
      R.canonical_quotient_mem_cut hp htpos hmemCanonical
    obtain ⟨hwrap, hsum, hpos, hdecomp0⟩ :=
      cutSaturationBadAt_span_n_sub_one_quotient_shape
        hp hcap C hn5 htpos hlam ht
        hdelta0 hdeltaHalf hc0 hcpi
        b hB hsupB hBadB R hvalues hspan
    let qOrd := (successiveDiffsFrom x0 xs).map Nat.floor
    let qWrap := Nat.floor (x0 + t - xs.getLastD x0)
    have hdecomp :
        R.gapQuotients t = qOrd ++ [qWrap] := by
      simpa [qOrd,qWrap] using hdecomp0
    have hwrap' : qWrap = 2 := by simpa [qWrap] using hwrap
    have hsum0 :
        qOrd.sum = n - 5 + 2 := by
      simpa [qOrd] using hsum
    have hsum' : qOrd.sum = n - 3 := by
      omega
    have hpos' : listPositiveCount qOrd = 1 := by
      have hp0 : listPositiveCount qOrd = 2 - 1 := by
        simpa [qOrd] using hpos
      omega
    rw [hdecomp, List.mem_append] at hmemCut
    rcases hmemCut with hOrd | hW
    · have hs :=
        list_sum_eq_member_of_positiveCount_one
          qOrd hpos' hOrd H.qe_ne
      rw [hsum'] at hs
      omega
    · simp only [List.mem_singleton] at hW
      rw [hwrap'] at hW
      exact hW

  have hsupportList :
      listPositiveCount (pre ++ qe :: post) = 2 := by
    rw [← hqCanon, ← centreQuotient_ofFn]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupB
  have hdelta1 : delta < 1 := by linarith
  have hsumFn :=
    deficit_three_support_two_sum
      (C b) (by omega : 4 ≤ n)
      hdelta0 hdelta1 ht hB hsupB
  have hsumList :
      (pre ++ qe :: post).sum = n - 1 := by
    rw [← hqCanon, ← centreQuotient_sum_eq_list_sum (C b) t]
    exact hsumFn

  have hhidden :
      SameSignQuotientOccurs (n - 3)
        (raySignAt hp b first)
        (liftedCentreSignPath hp b first rest)
        (quotientList t (C b).gaps) := by
    have hocc :=
      support_two_transition_hidden_sameSign
        (raySignAt hp b first)
        (liftedCentreSignPath hp b first rest)
        pre post qe (n - 1)
        hqe0 hsign hsupportList hsumList
    have hsub : (n - 1) - qe = n - 3 := by
      rw [hqe]
      omega
    rw [hsub] at hocc
    rw [hqCanon]
    exact hocc.2

  exact sameSignQuotient_pays_angle
    hp htpos hlam b (C b)
    first rest hrays (n - 3) hhidden

#print axioms cut_span_n_sub_one_support_two_transition_qe_eq_two
#print axioms cut_span_n_sub_one_support_two_hidden_angle_ge_n_sub_three

end JSP000404Research
