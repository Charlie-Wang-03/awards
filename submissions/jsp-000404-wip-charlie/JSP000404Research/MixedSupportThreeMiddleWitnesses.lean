import JSP000404Research.MixedSupportThreeNonExposed
import JSP000404Research.SixPointHardSupportReduction
import Mathlib.Tactic

/-!
# Two explicit middle-hidden three-transition witnesses in the mixed branch

The mixed support-one hard branch already forces two distinct non-exposed
support-three minima.  If compensated non-top deletion is excluded, both
centres must lie in the pinned middle-hidden branch.

This file keeps the two middle-hidden propositions and the two exact
three-transition witnesses together.  Downstream quantitative arguments can
therefore work directly with the quotient cycles instead of reconstructing
these facts from the coarser separated-pattern wrapper.
-/

namespace JSP000404Research

theorem mixed_support_one_has_two_middle_three_transition_centres
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
      positiveSupport (centreQuotient (C b) t) = 3 ∧
      positiveSupport (centreQuotient (C c) t) = 3 ∧
      SupportThreePinnedMiddleShape
        (t := t) hp (show top ≠ b by assumption) (C b) ∧
      SupportThreePinnedMiddleShape
        (t := t) hp (show top ≠ c by assumption) (C c) ∧
      (∃ first rest,
        (C b).rays = first :: rest ∧
        boolTransitionCountFrom
          (raySignAt hp b first)
          (liftedCentreSignPath hp b first rest) = 3) ∧
      (∃ first rest,
        (C c).rays = first :: rest ∧
        boolTransitionCountFrom
          (raySignAt hp c first)
          (liftedCentreSignPath hp c first rest) = 3) := by
  obtain ⟨b,c,
      hbTop,hcTop,hbA,hcA,hbc,
      hbSup3,hcSup3,hbTrans,hcTrans⟩ :=
    mixed_support_one_has_two_three_transition_centres
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top a hta hTop hMin hsupA

  have hbMiddle :
      SupportThreePinnedMiddleShape
        (t := t) hp (show top ≠ b by simpa using hbTop) (C b) :=
    support_three_middle_of_no_compensated_minimum_deletion
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top hTop hMin hNoMin hbTop hbSup3

  have hcMiddle :
      SupportThreePinnedMiddleShape
        (t := t) hp (show top ≠ c by simpa using hcTop) (C c) :=
    support_three_middle_of_no_compensated_minimum_deletion
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top hTop hMin hNoMin hcTop hcSup3

  exact ⟨b,c,
    hbTop,hcTop,hbA,hcA,hbc,
    hbSup3,hcSup3,
    hbMiddle,hcMiddle,hbTrans,hcTrans⟩

#print axioms mixed_support_one_has_two_middle_three_transition_centres

end JSP000404Research
