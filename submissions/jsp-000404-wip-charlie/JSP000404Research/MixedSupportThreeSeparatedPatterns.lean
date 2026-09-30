import JSP000404Research.MixedSupportThreeNonExposed
import JSP000404Research.SupportThreeMiddleHiddenSeparatedPattern
import JSP000404Research.SixPointHardSupportReduction
import Mathlib.Tactic

/-!
# Two enriched middle-hidden patterns in the mixed hard branch

In the six-point mixed branch, fix one support-one minimum a and assume that no
non-top deletion compensates the n-3 minimum layer.

The existing multiplicity argument supplies two distinct non-exposed
support-three minima b,c, each with exactly three sign transitions.  The
no-compensated-deletion hypothesis forces both pinned support-three cycles into
the middle-hidden shape.

Combining those facts with the enriched middle-hidden theorem yields two
ordered five-ray certificates which retain, simultaneously,

* the two delta-small zero-quotient edges;
* the three large positive-transition edges;
* the resulting three-cluster separation.

This is strictly stronger than the earlier pair of
SmallPerfectMatchingAwayFromTop certificates.
-/

namespace JSP000404Research

theorem mixed_support_one_has_two_separated_patterns
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta : ℝ} {n : ℕ}
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
      Nonempty
        (MiddleHiddenSeparatedPatternAwayFromTop
          p top b delta lam) ∧
      Nonempty
        (MiddleHiddenSeparatedPatternAwayFromTop
          p top c delta lam) := by
  obtain ⟨b,c,
      hbTop,hcTop,hbA,hcA,hbc,
      hbSup3,hcSup3,
      hbTrans,hcTrans⟩ :=
    mixed_support_one_has_two_three_transition_centres
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top a hta hTop hMin hsupA

  have hbMiddle :
      SupportThreePinnedMiddleShape hp
        (show top ≠ b by simpa using hbTop)
        (C b) :=
    support_three_middle_of_no_compensated_minimum_deletion
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top hTop hMin hNoMin hbTop hbSup3
  have hcMiddle :
      SupportThreePinnedMiddleShape hp
        (show top ≠ c by simpa using hcTop)
        (C c) :=
    support_three_middle_of_no_compensated_minimum_deletion
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top hTop hMin hNoMin hcTop hcSup3

  refine ⟨b,c,
    hbTop,hcTop,hbA,hcA,hbc,
    hbSup3,hcSup3,?_,?_⟩
  · exact support_three_middle_hidden_separated_pattern
      hp hcap (C b) hcard (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      hbTop (hMin b hbTop) hbSup3 hbMiddle hbTrans
  · exact support_three_middle_hidden_separated_pattern
      hp hcap (C c) hcard (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      hcTop (hMin c hcTop) hcSup3 hcMiddle hcTrans

#print axioms mixed_support_one_has_two_separated_patterns

end JSP000404Research
