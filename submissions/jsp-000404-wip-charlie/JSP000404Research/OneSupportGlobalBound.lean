import JSP000404Research.ConcreteOneSupportInterval
import JSP000404Research.StrictSupportAnglePacking
import JSP000404Research.OneSupportTurnPacking
import Mathlib.Tactic

/-!
# Global dyadic bound for all one-support centres

This file closes the support=1 regime completely.

For each centre, ConcreteOneSupportInterval supplies

  q_i = k_i + 1,
  q_i <= t * g_i,
  width_i = pi * (1 - g_i),

together with a common-signed interval representation of every ray.

Different centres have disjoint strict-support angle balls, so the angle-circle
packing theorem gives

  sum_i (pi - width_i) <= 2*pi,

hence

  sum_i g_i <= 2.

The transition-gap packing theorem then yields

  sum_i 2^(k_i) <= 2^n

in the lower branch delta < 1/2.

Thus support=1 is no longer part of the unresolved JSP-000404 gap.
-/

namespace JSP000404Research

open Real
open scoped BigOperators

structure OneSupportIntervalCertificate
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (t : ℝ) (i : V)
    (C : CentreProjectiveCycle hp i) where
  qe : ℕ
  ge : ℝ
  a : ℝ
  width : ℝ
  sigma : Bool
  qe_ne : qe ≠ 0
  qe_eq : qe = centreExponent C t + 1
  qe_le : (qe : ℝ) ≤ t * ge
  ge_pos : 0 < ge
  width_eq : width = Real.pi * (1 - ge)
  width_nonneg : 0 ≤ width
  width_lt_pi : width < Real.pi
  repr : ∀ j, j ≠ i →
    ∃ rho : ℝ, ∃ theta : ℝ,
      0 < rho ∧
      a ≤ theta ∧ theta ≤ a + width ∧
      p j - p i =
        rho • signedRayDirection sigma theta

/-- Every concrete support-one centre admits the packaged certificate. -/
theorem exists_oneSupportIntervalCertificate
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
    Nonempty (OneSupportIntervalCertificate hp t i C) := by
  obtain ⟨qe, ge, a, width, sigma,
      hqe, hqeEq, hqeLe, hge,
      hwidthEq, hwidth0, hwidthPi, hrepr⟩ :=
    concrete_one_support_interval_certificate
      hp hcap hn hdelta0 ht hlam i C hsupport
  exact ⟨{
    qe := qe
    ge := ge
    a := a
    width := width
    sigma := sigma
    qe_ne := hqe
    qe_eq := hqeEq
    qe_le := hqeLe
    ge_pos := hge
    width_eq := hwidthEq
    width_nonneg := hwidth0
    width_lt_pi := hwidthPi
    repr := hrepr
  }⟩

/-- One-support centres automatically have exponent < n in the delta<1
normalization. -/
theorem centreExponent_lt_n_of_support_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (n : ℕ) (delta t : ℝ)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hsupport :
      positiveSupport (centreQuotient C t) = 1) :
    centreExponent C t < n := by
  have hsum :=
    centreQuotient_function_sum_le_n
      C n delta t hn hdelta0 hdelta1 ht
  have hid :=
    floorExcess_add_positiveSupport
      (centreQuotient C t)
  have heq :
      centreExponent C t + 1 =
        ∑ r, centreQuotient C t r := by
    simpa [centreExponent, hsupport] using hid
  rw [← heq] at hsum
  omega

/-- Exact gap-packing consequence for any finite family of distinct actual
support-one centres. -/
theorem oneSupport_gap_sum_le_two
    {V I : Type*} [LinearOrder V] [Fintype V] [Fintype I]
    {p : V → Plane}
    (hp : Function.Injective p)
    (centre : I → V)
    (hcentre : Function.Injective centre)
    (t : ℝ)
    (C : ∀ r : I, CentreProjectiveCycle hp (centre r))
    (cert : ∀ r : I,
      OneSupportIntervalCertificate hp t (centre r) (C r)) :
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

/-- Final closed theorem for the support-one stratum. -/
theorem oneSupport_centres_dyadic_sum_le_two_pow
    {V I : Type*} [LinearOrder V] [Fintype V] [Fintype I]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (centre : I → V)
    (hcentre : Function.Injective centre)
    (C : ∀ r : I, CentreProjectiveCycle hp (centre r))
    (hsupport : ∀ r : I,
      positiveSupport (centreQuotient (C r) t) = 1) :
    (∑ r : I, 2 ^ centreExponent (C r) t) ≤ 2 ^ n := by
  classical
  let cert : ∀ r : I,
      OneSupportIntervalCertificate hp t (centre r) (C r) :=
    fun r =>
      Classical.choice
        (exists_oneSupportIntervalCertificate
          hp hcap hn hdelta0 ht hlam
          (centre r) (C r) (hsupport r))
  have hgap :
      (∑ r : I, (cert r).ge) ≤ 2 :=
    oneSupport_gap_sum_le_two
      hp centre hcentre t C cert
  have hexp :
      ∀ r : I, centreExponent (C r) t < n := by
    intro r
    exact centreExponent_lt_n_of_support_one
      (C r) n delta t hn hdelta0
      (by linarith) ht (hsupport r)
  exact dyadic_sum_le_two_pow_of_transition_gap_packing
    (exponent := fun r => centreExponent (C r) t)
    (quotient := fun r => (cert r).qe)
    (gap := fun r => (cert r).ge)
    n delta t hn hdelta0 hdeltaHalf ht
    hexp
    (fun r => (cert r).qe_eq)
    (fun r => (cert r).qe_le)
    hgap

#print axioms exists_oneSupportIntervalCertificate
#print axioms centreExponent_lt_n_of_support_one
#print axioms oneSupport_gap_sum_le_two
#print axioms oneSupport_centres_dyadic_sum_le_two_pow

end JSP000404Research
