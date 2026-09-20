import JSP000404Research.ConcreteTransitionInterval
import JSP000404Research.StrictSupportAnglePacking
import JSP000404Research.OneSupportTurnPacking
import Mathlib.Tactic

/-!
# Global packing of transition gaps for high-exponent centres

Every centre with exponent at least n-2 has a quantitative transition interval.
The dual strict-support arc has normalized length ge, so distinct centres have
disjoint support arcs and

  sum ge <= 2.

Since each transition quotient satisfies qe <= t*ge, in the lower branch this
implies

  sum qe <= 2*n.

This file also proves that if such a centre has quotient support one, then its
transition quotient is exactly exponent+1.
-/

namespace JSP000404Research

open Real
open scoped BigOperators

/-- In a list with exactly one positive entry, any displayed nonzero member is
the whole list sum. -/
theorem list_sum_eq_member_of_positiveCount_one
    (qs : List ℕ) (q : ℕ)
    (hsupport : listPositiveCount qs = 1)
    (hqmem : q ∈ qs)
    (hqne : q ≠ 0) :
    qs.sum = q := by
  induction qs with
  | nil =>
      simp at hqmem
  | cons a as ih =>
      rw [List.mem_cons] at hqmem
      by_cases ha : a = 0
      · subst a
        simp only [listPositiveCount, if_pos rfl, zero_add] at hsupport
        simp only [List.sum_cons, zero_add]
        rcases hqmem with hq | hq
        · exact False.elim (hqne hq.symm)
        · exact ih hsupport hq hqne
      · simp only [listPositiveCount, if_neg ha] at hsupport
        have htailCount : listPositiveCount as = 0 := by omega
        have htailSum :=
          list_sum_eq_zero_of_positiveCount_eq_zero as htailCount
        rcases hqmem with hq | hq
        · subst q
          simp [htailSum]
        · have hqzero : q = 0 := by
            have hallzero :
                ∀ x ∈ as, x = 0 := by
              intro x hx
              by_contra hx0
              have hpos :
                  1 ≤ listPositiveCount as := by
                induction as with
                | nil => simp at hx
                | cons b bs ih2 =>
                    by_cases hb : b = 0
                    · subst b
                      simp only [listPositiveCount, if_pos rfl, zero_add]
                      rw [List.mem_cons] at hx
                      rcases hx with rfl | hx
                      · contradiction
                      · exact ih2 hx
                    · simp [listPositiveCount, hb]
              omega
            exact hallzero q hq
          exact False.elim (hqne hqzero)

/-- For a support-one high-exponent centre, the transition quotient is exactly
the usual one-support turn cost exponent+1. -/
theorem highTransition_qe_eq_exponent_add_one_of_support_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} {t : ℝ}
    (C : CentreProjectiveCycle hp i)
    (cert : HighExponentTransitionIntervalCertificate hp t i C)
    (hsupport :
      positiveSupport (centreQuotient C t) = 1) :
    cert.qe = centreExponent C t + 1 := by
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) = 1 := by
    rw [← centreQuotient_ofFn]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  have hsumList :
      (quotientList t C.gaps).sum = cert.qe :=
    list_sum_eq_member_of_positiveCount_one
      (quotientList t C.gaps) cert.qe
      hsupportList cert.qe_mem cert.qe_ne
  have hid :=
    floorExcess_add_positiveSupport (centreQuotient C t)
  have hid' :
      centreExponent C t + 1 =
        ∑ r, centreQuotient C t r := by
    simpa [centreExponent, hsupport] using hid
  rw [centreQuotient_sum_eq_list_sum C t, hsumList] at hid'
  omega

/-- Strict-support arcs of any finite family of distinct high-exponent centres
pack into the full direction circle. -/
theorem highTransition_gap_sum_le_two
    {V I : Type*} [LinearOrder V] [Fintype V] [Fintype I]
    {p : V → Plane}
    (hp : Function.Injective p)
    (centre : I → V)
    (hcentre : Function.Injective centre)
    (t : ℝ)
    (C : ∀ r : I, CentreProjectiveCycle hp (centre r))
    (cert : ∀ r : I,
      HighExponentTransitionIntervalCertificate hp t (centre r) (C r)) :
    (∑ r : I, (cert r).ge) ≤ 2 := by
  have hpack :=
    strict_support_arc_width_sum_le_two_pi
      (p := p)
      centre hcentre
      (fun r => (cert r).a)
      (fun r => (cert r).width)
      (fun r => (cert r).sigma)
      (fun r => (cert r).width_nonneg)
      (fun r => (cert r).width_lt_pi)
      (fun r => (cert r).repr)
  have hterm :
      ∀ r : I,
        Real.pi - (cert r).width =
          Real.pi * (cert r).ge := by
    intro r
    rw [(cert r).width_eq]
    ring
  have hsumEq :
      (∑ r : I, (Real.pi - (cert r).width)) =
        Real.pi * (∑ r : I, (cert r).ge) := by
    calc
      (∑ r : I, (Real.pi - (cert r).width))
          = ∑ r : I, Real.pi * (cert r).ge := by
              apply Finset.sum_congr rfl
              intro r _
              exact hterm r
      _ = Real.pi * (∑ r : I, (cert r).ge) := by
          rw [Finset.mul_sum]
  rw [hsumEq] at hpack
  nlinarith [Real.pi_pos]

/-- In the lower branch, transition quotients of any finite family of
high-exponent centres have total at most 2n. -/
theorem highTransition_quotient_sum_le_two_n
    {V I : Type*} [LinearOrder V] [Fintype V] [Fintype I]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (centre : I → V)
    (hcentre : Function.Injective centre)
    (C : ∀ r : I, CentreProjectiveCycle hp (centre r))
    (cert : ∀ r : I,
      HighExponentTransitionIntervalCertificate hp t (centre r) (C r)) :
    (∑ r : I, (cert r).qe) ≤ 2 * n := by
  exact sum_quotient_le_two_n_of_transition_gap_packing
    (fun r => (cert r).qe)
    (fun r => (cert r).ge)
    n delta t hn hdelta0 hdeltaHalf ht
    (fun r => (cert r).qe_le)
    (highTransition_gap_sum_le_two
      hp centre hcentre t C cert)

#print axioms list_sum_eq_member_of_positiveCount_one
#print axioms highTransition_qe_eq_exponent_add_one_of_support_one
#print axioms highTransition_gap_sum_le_two
#print axioms highTransition_quotient_sum_le_two_n

end JSP000404Research
