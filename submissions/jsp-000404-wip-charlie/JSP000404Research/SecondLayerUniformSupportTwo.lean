import JSP000404Research.SecondLayerFourSupportReduction
import Mathlib.Tactic

/-!
# Compatibility aliases for the uniform four-second-layer reduction

The canonical implementation lives in SecondLayerFourSupportReduction.lean.
This file only exposes the names used by the multiplicity-first Q/T/T/T branch
and adds one explicit-certificate arithmetic corollary.
-/

namespace JSP000404Research

theorem four_secondLayer_has_two_supportTwo_uniform
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (haSecond : centreExponent (C a) t = n - 2)
    (hbSecond : centreExponent (C b) t = n - 2)
    (hcSecond : centreExponent (C c) t = n - 2)
    (hdSecond : centreExponent (C d) t = n - 2) :
    ∃ x y : V,
      x ≠ y ∧
      x ∈ ({a,b,c,d} : Finset V) ∧
      y ∈ ({a,b,c,d} : Finset V) ∧
      positiveSupport (centreQuotient (C x) t) = 2 ∧
      positiveSupport (centreQuotient (C y) t) = 2 :=
  four_secondLayer_has_two_supportTwo_of_three_le_n
    hp hcap hn3 hdelta0 hdeltaHalf ht hlam C
    hab hac had hbc hbd hcd
    haSecond hbSecond hcSecond hdSecond

theorem four_secondLayer_exact_two_supportTwo_force_unit_transitions
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (Cd : CentreProjectiveCycle hp d)
    (certA : HighExponentTransitionIntervalCertificate hp t a Ca)
    (certB : HighExponentTransitionIntervalCertificate hp t b Cb)
    (certC : HighExponentTransitionIntervalCertificate hp t c Cc)
    (certD : HighExponentTransitionIntervalCertificate hp t d Cd)
    (_haSecond : centreExponent Ca t = n - 2)
    (_hbSecond : centreExponent Cb t = n - 2)
    (hcSecond : centreExponent Cc t = n - 2)
    (hdSecond : centreExponent Cd t = n - 2)
    (_haSupport : positiveSupport (centreQuotient Ca t) = 2)
    (_hbSupport : positiveSupport (centreQuotient Cb t) = 2)
    (hcSupport : positiveSupport (centreQuotient Cc t) = 1)
    (hdSupport : positiveSupport (centreQuotient Cd t) = 1) :
    certA.qe = 1 ∧ certB.qe = 1 := by
  have hqC :
      certC.qe = n - 1 :=
    deficit_two_support_one_transition_qe_eq
      Cc certC hn3 hcSecond hcSupport
  have hqD :
      certD.qe = n - 1 :=
    deficit_two_support_one_transition_qe_eq
      Cd certD hn3 hdSecond hdSupport
  have hqApos : 1 ≤ certA.qe :=
    Nat.one_le_iff_ne_zero.mpr certA.qe_ne
  have hqBpos : 1 ≤ certB.qe :=
    Nat.one_le_iff_ne_zero.mpr certB.qe_ne
  have hpack :=
    four_transition_quotient_sum_le_two_n
      hp (by omega : 1 ≤ n)
      hdelta0 hdeltaHalf ht
      hab hac had hbc hbd hcd
      Ca Cb Cc Cd certA certB certC certD
  rw [hqC,hqD] at hpack
  constructor <;> omega

#print axioms four_secondLayer_has_two_supportTwo_uniform
#print axioms four_secondLayer_exact_two_supportTwo_force_unit_transitions

end JSP000404Research
