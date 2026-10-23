import JSP000404Research.MixedSupportThreeNonExposed
import JSP000404Research.SixPointHardSupportReduction
import Mathlib.Tactic

/-!
# Surviving six-point mixed hard terminal: two triple-transition middle-hidden minima

This connects two independently certified geometric constraints.  If a
six-centre top-plus-five-third-layer configuration has a support-one minimum
and NO compensated deletion of a minimum, then two further distinct minima
are simultaneously:
* non-strictly-exposed support-three centres;
* equipped with three concrete sign transitions; and
* pinned middle-hidden with respect to the sharp top ray.

This is a necessary profile for the remaining hard case, not an
all-six-source Boolean payment and not an exclusion of the profile.
-/

namespace JSP000404Research

theorem six_point_mixed_no_minimum_deletion_two_hidden_three_transition_centres
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
      ∀ v : V, v ≠ top → centreExponent (C v) t = n - 3)
    (hsupA : positiveSupport (centreQuotient (C a) t) = 1)
    (hNoMin :
      SixPointNoCompensatedMinimumDeletion
        C (by rw [hcard]; omega) top t n) :
    ∃ b c : V,
      b ≠ top ∧ c ≠ top ∧
      b ≠ a ∧ c ≠ a ∧ b ≠ c ∧
      positiveSupport (centreQuotient (C b) t) = 3 ∧
      positiveSupport (centreQuotient (C c) t) = 3 ∧
      (∃ first rest,
        (C b).rays = first :: rest ∧
        boolTransitionCountFrom
          (raySignAt hp b first)
          (liftedCentreSignPath hp b first rest) = 3) ∧
      (∃ first rest,
        (C c).rays = first :: rest ∧
        boolTransitionCountFrom
          (raySignAt hp c first)
          (liftedCentreSignPath hp c first rest) = 3) ∧
      (∃ hb : top ≠ b,
        SupportThreePinnedMiddleShape (t := t) hp hb (C b)) ∧
      (∃ hc : top ≠ c,
        SupportThreePinnedMiddleShape (t := t) hp hc (C c)) := by
  obtain ⟨b, c, hbTop, hcTop, hbA, hcA, hbc,
      hbSup3, hcSup3, hbTrans, hcTrans⟩ :=
    mixed_support_one_has_two_three_transition_centres
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top a hta hTop hMin hsupA
  have hbMiddle :=
    support_three_middle_of_no_compensated_minimum_deletion
      hp hcap C hcard hn5 hdelta0 hdeltaHalf ht hlam
      top hTop hMin hNoMin hbTop hbSup3
  have hcMiddle :=
    support_three_middle_of_no_compensated_minimum_deletion
      hp hcap C hcard hn5 hdelta0 hdeltaHalf ht hlam
      top hTop hMin hNoMin hcTop hcSup3
  exact ⟨b, c, hbTop, hcTop, hbA, hcA, hbc,
    hbSup3, hcSup3, hbTrans, hcTrans,
    ⟨hbTop.symm, hbMiddle⟩, ⟨hcTop.symm, hcMiddle⟩⟩

#print axioms six_point_mixed_no_minimum_deletion_two_hidden_three_transition_centres

end JSP000404Research
