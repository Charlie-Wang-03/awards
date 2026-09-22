import JSP000404Research.HighExponentTransitionPacking
import JSP000404Research.ConcreteTransitionInterval
import Mathlib.Tactic

/-!
# Multiplicity bounds for one-support centres in the top two layers

For every centre with

  exponent >= n-2
  positiveSupport = 1,

the distinguished transition quotient equals exponent+1 and is therefore at
least n-1.

Strict-support arc packing gives total transition quotient at most 2n.
Consequently any finite injective family of such centres satisfies

  card(I) * (n-1) <= 2n.

In particular, for n>=4 there are at most two one-support centres in the top
two exponent layers.  The genuinely difficult second-layer population is
therefore the support-two, deficit-two regime.
-/

namespace JSP000404Research

open scoped BigOperators

theorem oneSupportHigh_family_card_mul_le_two_n
    {V I : Type*}
    [LinearOrder V] [Fintype V] [Fintype I]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (centre : I → V)
    (hcentre : Function.Injective centre)
    (C : ∀ r : I, CentreProjectiveCycle hp (centre r))
    (hlarge :
      ∀ r : I, n - 2 ≤ centreExponent (C r) t)
    (hsupport :
      ∀ r : I,
        positiveSupport (centreQuotient (C r) t) = 1) :
    Fintype.card I * (n - 1) ≤ 2 * n := by
  have hdelta1 : delta < 1 := by linarith
  let cert :
      ∀ r : I,
        HighExponentTransitionIntervalCertificate
          hp t (centre r) (C r) :=
    fun r =>
      Classical.choice
        (exists_highExponentTransitionIntervalCertificate
          hp hcap (by omega : 1 ≤ n)
          hdelta0 hdelta1 ht hlam
          (centre r) (C r) (hlarge r))
  have hqLower :
      ∀ r : I, n - 1 ≤ (cert r).qe := by
    intro r
    have hqe :=
      highTransition_qe_eq_exponent_add_one_of_support_one
        (C r) (cert r) (hsupport r)
    rw [hqe]
    have hk := hlarge r
    omega
  have hsumLower :
      Fintype.card I * (n - 1) ≤
        ∑ r : I, (cert r).qe := by
    have h :=
      Finset.sum_le_sum
        (s := (Finset.univ : Finset I))
        (fun r _ => hqLower r)
    simpa [Finset.sum_const, Nat.mul_comm] using h
  have hsumUpper :
      (∑ r : I, (cert r).qe) ≤ 2 * n :=
    highTransition_quotient_sum_le_two_n
      hp (by omega : 1 ≤ n)
      hdelta0 hdeltaHalf ht
      centre hcentre C cert
  exact hsumLower.trans hsumUpper

theorem oneSupportHigh_family_card_le_two
    {V I : Type*}
    [LinearOrder V] [Fintype V] [Fintype I]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (centre : I → V)
    (hcentre : Function.Injective centre)
    (C : ∀ r : I, CentreProjectiveCycle hp (centre r))
    (hlarge :
      ∀ r : I, n - 2 ≤ centreExponent (C r) t)
    (hsupport :
      ∀ r : I,
        positiveSupport (centreQuotient (C r) t) = 1) :
    Fintype.card I ≤ 2 := by
  have h :=
    oneSupportHigh_family_card_mul_le_two_n
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      centre hcentre C hlarge hsupport
  nlinarith

/-- At n=3 the same packing gives the weaker sharp bound of three. -/
theorem oneSupportHigh_family_card_le_three_at_three
    {V I : Type*}
    [LinearOrder V] [Fintype V] [Fintype I]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (centre : I → V)
    (hcentre : Function.Injective centre)
    (C : ∀ r : I, CentreProjectiveCycle hp (centre r))
    (hlarge :
      ∀ r : I, 1 ≤ centreExponent (C r) t)
    (hsupport :
      ∀ r : I,
        positiveSupport (centreQuotient (C r) t) = 1) :
    Fintype.card I ≤ 3 := by
  have h :=
    oneSupportHigh_family_card_mul_le_two_n
      hp hcap (n := 3) (by omega)
      hdelta0 hdeltaHalf ht hlam
      centre hcentre C
      (by simpa using hlarge) hsupport
  norm_num at h
  omega

#print axioms oneSupportHigh_family_card_mul_le_two_n
#print axioms oneSupportHigh_family_card_le_two

end JSP000404Research
