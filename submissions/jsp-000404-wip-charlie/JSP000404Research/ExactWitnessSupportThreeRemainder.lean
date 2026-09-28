import JSP000404Research.ExactWitnessCanonicalUnitGap
import JSP000404Research.DeficitThreeSupportThreeRemainder
import Mathlib.Tactic

/-!
# Exact unit-gap remainder package in the support-three witness branch

At a six-point exact maximum-angle witness centre in the n-3 / support-three
branch there is a canonical cyclic gap e with

  centreQuotient e = 1,
  t * gap(e) = 1.

Hence the fractional remainder at e is exactly zero.

Independently, the total support-three quotient mass is n, so every aligned
gap remainder lies in [0,delta].  This packages both facts at one dependent
index for the final pinned-position analysis.
-/

namespace JSP000404Research

theorem exists_exactWitness_support_three_zero_remainder_gap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3) :
    ∃ e : Fin C.gaps.length,
      centreQuotient C t e = 1 ∧
      t * C.gaps.get e = 1 ∧
      t * C.gaps.get e -
          (centreQuotient C t e : ℝ) = 0 ∧
      ∀ r : Fin C.gaps.length,
        0 ≤
            t * C.gaps.get r -
              (centreQuotient C t r : ℝ)
          ∧
        t * C.gaps.get r -
              (centreQuotient C t r : ℝ)
          ≤ delta := by
  obtain ⟨e, heq, hscaled⟩ :=
    exists_exactWitness_canonical_unit_gap
      hp hcap (by omega : 3 ≤ n)
      hdelta0 ht hlam W C
  refine ⟨e, heq, hscaled, ?_, ?_⟩
  · rw [hscaled, heq]
    norm_num
  · intro r
    exact
      centre_gap_remainder_between_zero_delta_of_deficit_three_support_three
        C hn hdelta0 hdeltaHalf ht hexp hsupport r

/-- The exact witness gap is the unique place where the packaged theorem
certifies zero remainder; any chosen pinned position carrying that same
canonical gap therefore has exact integer scaled width. -/
theorem exactWitness_support_three_gap_remainder_zero
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3) :
    ∃ e : Fin C.gaps.length,
      t * C.gaps.get e -
        (centreQuotient C t e : ℝ) = 0 := by
  obtain ⟨e, _heq, _hscaled, hzero, _hall⟩ :=
    exists_exactWitness_support_three_zero_remainder_gap
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      W C hexp hsupport
  exact ⟨e, hzero⟩

#print axioms exists_exactWitness_support_three_zero_remainder_gap
#print axioms exactWitness_support_three_gap_remainder_zero

end JSP000404Research
