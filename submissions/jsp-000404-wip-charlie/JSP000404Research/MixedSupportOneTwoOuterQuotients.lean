import JSP000404Research.MixedSupportThreeMiddleWitnesses
import JSP000404Research.MixedSupportOneOuterQuotientBound
import Mathlib.Tactic

/-!
# Two bounded outer quotients in the mixed hard branch

The mixed support-one hard branch contains two distinct middle-hidden
support-three minima b,c with three sign transitions.  Applying the aligned
support-one outer-quotient theorem at each centre gives explicit cycle
certificates Hb,Hc such that each has at least one outer positive quotient at
most three.

This keeps the two quotient bounds simultaneously for the remaining finite
six-point analysis.
-/

namespace JSP000404Research

theorem mixed_support_one_has_two_outer_quotients_le_three
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top a : V)
    (hta : top ≠ a)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient (C a) t) = 1)
    (hNoMin :
      SixPointNoCompensatedMinimumDeletion
        C (by rw [hcard]; omega) top t n) :
    ∃ b c : V,
      b ≠ top ∧ c ≠ top ∧
      b ≠ a ∧ c ≠ a ∧ b ≠ c ∧
      ∃ Hb : MiddleHiddenPinnedCycleCertificate
          hp top b (show top ≠ b by assumption) (C b) t,
      ∃ Hc : MiddleHiddenPinnedCycleCertificate
          hp top c (show top ≠ c by assumption) (C c) t,
        (Hb.qFirst ≤ 3 ∨ Hb.qLast ≤ 3) ∧
        (Hc.qFirst ≤ 3 ∨ Hc.qLast ≤ 3) := by
  obtain ⟨b,c,
      hbTop,hcTop,hbA,hcA,hbc,
      hbSup3,hcSup3,
      hbMiddle,hcMiddle,
      hbTrans,hcTrans⟩ :=
    mixed_support_one_has_two_middle_three_transition_centres
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top a hta hTop hMin hsupA hNoMin

  obtain ⟨Hb,hbBound⟩ :=
    middle_hidden_outer_quotient_le_three_of_support_one
      hp hcap hcard (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      hta hbTop hbA.symm
      (C top) (C a) (C b)
      hTop (hMin a hta.symm) hsupA
      (hMin b hbTop) hbSup3
      hbMiddle hbTrans

  obtain ⟨Hc,hcBound⟩ :=
    middle_hidden_outer_quotient_le_three_of_support_one
      hp hcap hcard (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      hta hcTop hcA.symm
      (C top) (C a) (C c)
      hTop (hMin a hta.symm) hsupA
      (hMin c hcTop) hcSup3
      hcMiddle hcTrans

  exact ⟨b,c,
    hbTop,hcTop,hbA,hcA,hbc,
    Hb,Hc,hbBound,hcBound⟩

#print axioms mixed_support_one_has_two_outer_quotients_le_three

end JSP000404Research
