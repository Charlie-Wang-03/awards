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
  classical
  have hmemFn :
      cert.qe ∈ List.ofFn (centreQuotient C t) := by
    rw [centreQuotient_ofFn C t]
    exact cert.qe_mem
  rw [List.mem_ofFn'] at hmemFn
  obtain ⟨r, hr⟩ := hmemFn
  have hrpos : centreQuotient C t r ≠ 0 := by
    rw [hr]
    exact cert.qe_ne
  obtain ⟨e, hepos, heuniq⟩ :=
    existsUnique_positive_of_one_support
      (centreQuotient C t) hsupport
  have hre : r = e := heuniq r hrpos
  have hsumSingle :
      (∑ x, centreQuotient C t x) =
        centreQuotient C t r := by
    apply Finset.sum_eq_single r
    · intro x _ hxr
      by_contra hxpos
      have hxe : x = e := heuniq x hxpos
      exact hxr (hxe.trans hre.symm)
    · simp
  have hid :=
    floorExcess_add_positiveSupport (centreQuotient C t)
  have hid' :
      centreExponent C t + 1 =
        ∑ x, centreQuotient C t x := by
    simpa [centreExponent, hsupport] using hid
  rw [hsumSingle, hr] at hid'
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

#print axioms highTransition_qe_eq_exponent_add_one_of_support_one
#print axioms highTransition_gap_sum_le_two
#print axioms highTransition_quotient_sum_le_two_n

end JSP000404Research
