import JSP000404Research.CentreSignPath
import JSP000404Research.TransitionGapAlignment
import JSP000404Research.DyadicTurnCost
import JSP000404Research.LinearizedTransitionExposure
import Mathlib.Tactic

/-!
# Concrete turn cost of a one-support centre

For an actual centre projective cycle, assume the Sendov quotient support is
exactly one.

The concrete sign-path theorem supplies one sign transition and the transition
must lie at the unique positive quotient.  Therefore the distinguished
transition quotient equals

  centreExponent + 1.

Alignment with the actual normalized projective gap then gives

  (centreExponent + 1) * lambda <= pi * transitionGap.

This is the quantitative bridge from dyadic exponent to geometric turn cost
for the one-support regime.
-/

namespace JSP000404Research

open scoped BigOperators
open Real

theorem listPositiveCount_append
    (xs ys : List ℕ) :
    listPositiveCount (xs ++ ys) =
      listPositiveCount xs + listPositiveCount ys := by
  induction xs with
  | nil => simp [listPositiveCount]
  | cons q qs ih =>
      simp [listPositiveCount, ih, Nat.add_assoc]

theorem list_sum_eq_zero_of_positiveCount_eq_zero
    (qs : List ℕ)
    (h : listPositiveCount qs = 0) :
    qs.sum = 0 := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
      by_cases hq : q = 0
      · subst q
        simp only [listPositiveCount, if_pos rfl, zero_add] at h
        simp [ih h]
      · simp [listPositiveCount, hq] at h

/-- In a one-support list, any displayed positive entry is the whole list
sum. -/
theorem distinguished_positive_eq_list_sum_of_support_one
    (pre post : List ℕ) (qe : ℕ)
    (hqe : qe ≠ 0)
    (hsupport :
      listPositiveCount (pre ++ qe :: post) = 1) :
    (pre ++ qe :: post).sum = qe := by
  have hc := hsupport
  rw [listPositiveCount_append] at hc
  simp only [listPositiveCount, if_neg hqe] at hc
  have hpre : listPositiveCount pre = 0 := by omega
  have hpost : listPositiveCount post = 0 := by omega
  have hpreSum :=
    list_sum_eq_zero_of_positiveCount_eq_zero pre hpre
  have hpostSum :=
    list_sum_eq_zero_of_positiveCount_eq_zero post hpost
  simp [hpreSum, hpostSum]

/-- Actual one-support centre: the unique transition quotient is exponent+1
and pays that many cap units of projective angular width. -/
theorem concrete_one_support_transition_cost
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (hsupport :
      positiveSupport (centreQuotient C t) = 1) :
    ∃ pre post : List ℕ,
      ∃ qe : ℕ,
      ∃ gpre gpost : List ℝ,
      ∃ ge : ℝ,
        qe ≠ 0 ∧
        quotientList t C.gaps = pre ++ qe :: post ∧
        C.gaps = gpre ++ ge :: gpost ∧
        gpre.length = pre.length ∧
        gpost.length = post.length ∧
        qe = centreExponent C t + 1 ∧
        (qe : ℝ) ≤ t * ge ∧
        0 < ge ∧
        ((centreExponent C t + 1 : ℕ) : ℝ) * lam
          ≤ Real.pi * ge := by
  obtain ⟨first, rest, hrays⟩ :
      ∃ first rest, C.rays = first :: rest := by
    cases h : C.rays with
    | nil =>
        exact False.elim (C.nonempty h)
    | cons first rest =>
        exact ⟨first, rest, h⟩
  have ht1 : 1 ≤ t :=
    sendov_scale_one_le hn hdelta0 ht
  have htpos : 0 < t :=
    lt_of_lt_of_le zero_lt_one ht1
  have hchanges :
      ChangesOnlyOnPositive
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
        (quotientList t C.gaps) :=
    centre_changesOnlyOnPositive
      hp hcap htpos ht1 hlam i C first rest hrays
  have hlast :
      boolLastFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest)
        =
      !raySignAt hp i first :=
    liftedCentreSignPath_last_not hp i first rest
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) = 1 := by
    rw [← centreQuotient_ofFn]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  obtain ⟨pre, post, qe, hqe, hq, _hsigns⟩ :=
    antiperiodic_positive_transition_gap_of_support_le_two
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps)
      hchanges hlast
      (by omega : listPositiveCount (quotientList t C.gaps) ≤ 2)
  have hsupportDecomp :
      listPositiveCount (pre ++ qe :: post) = 1 := by
    rw [← hq]
    exact hsupportList
  have hlistSum :
      (quotientList t C.gaps).sum = qe := by
    rw [hq]
    exact distinguished_positive_eq_list_sum_of_support_one
      pre post qe hqe hsupportDecomp
  have hqeExp :
      qe = centreExponent C t + 1 := by
    have hid :=
      floorExcess_add_positiveSupport (centreQuotient C t)
    have hid' :
        centreExponent C t + 1 =
          ∑ r, centreQuotient C t r := by
      simpa [centreExponent, hsupport] using hid
    rw [centreQuotient_sum_eq_list_sum C t, hlistSum] at hid'
    omega
  have halign0 :
      QuotientGapAligned t (quotientList t C.gaps) C.gaps :=
    centreQuotient_aligned C htpos.le
  have halign :
      QuotientGapAligned t (pre ++ qe :: post) C.gaps := by
    rwa [← hq]
  obtain ⟨gpre, gpost, ge, hgaps, hpreLen, hpostLen,
      hqeGap, _hpreAlign, _hpostAlign⟩ :=
    aligned_gap_decomposition halign
  have hgePos :
      0 < ge :=
    aligned_transition_gap_pos htpos hqe hqeGap
  have hangle0 :
      (qe : ℝ) * lam ≤ Real.pi * ge :=
    quotient_mul_lam_le_pi_mul_gap
      htpos hqeGap hlam
  have hangle :
      ((centreExponent C t + 1 : ℕ) : ℝ) * lam
        ≤ Real.pi * ge := by
    rw [← hqeExp]
    exact hangle0
  exact ⟨pre, post, qe, gpre, gpost, ge,
    hqe, hq, hgaps, hpreLen, hpostLen,
    hqeExp, hqeGap, hgePos, hangle⟩

#print axioms distinguished_positive_eq_list_sum_of_support_one
#print axioms concrete_one_support_transition_cost

end JSP000404Research
