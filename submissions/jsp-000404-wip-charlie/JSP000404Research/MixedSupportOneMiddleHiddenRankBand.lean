import JSP000404Research.MixedSupportThreeNonExposed
import JSP000404Research.MiddleHiddenCanonicalRankBand
import JSP000404Research.SixPointHardSupportReduction
import Mathlib.Tactic

/-!
# Mixed support-one branch: middle-hidden rank bands on the same side

This module is a glue result only.  It introduces no new geometric estimate.

In the six-point mixed hard branch, a support-one minimum forces two distinct
non-exposed support-three minima.  If compensated minimum deletion is excluded,
the existing hard-support reduction puts both centres in the pinned
middle-hidden shape.  The canonical-sign analysis then gives a rank band for
each centre, and the rank-band terminal shows that the two centres must lie on
the same side of the distinguished top vertex in the canonical point order.

This packages the latest middle-hidden order information directly at the
mixed-branch level for downstream terminal arguments.
-/

namespace JSP000404Research

theorem mixed_support_one_two_middle_hidden_rank_bands_same_side
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
      MiddleHiddenRankBand p top b ∧
      MiddleHiddenRankBand p top c ∧
      ((CanonicalPointLt p b top ∧ CanonicalPointLt p c top) ∨
       (CanonicalPointLt p top b ∧ CanonicalPointLt p top c)) := by
  obtain ⟨b,c,
      hbTop,hcTop,hbA,hcA,hbc,
      hbSup3,hcSup3,hbNotExp,hcNotExp⟩ :=
    mixed_support_one_has_two_nonexposed_support_three
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top a hta hTop hMin hsupA

  have hbMiddle :
      SupportThreePinnedMiddleShape
        (t := t) hp
        (show top ≠ b by simpa using hbTop)
        (C b) :=
    support_three_middle_of_no_compensated_minimum_deletion
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top hTop hMin hNoMin hbTop hbSup3
  have hcMiddle :
      SupportThreePinnedMiddleShape
        (t := t) hp
        (show top ≠ c by simpa using hcTop)
        (C c) :=
    support_three_middle_of_no_compensated_minimum_deletion
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top hTop hMin hNoMin hcTop hcSup3

  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :
      1 ≤ t :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht

  have hbBand :
      MiddleHiddenRankBand p top b :=
    nonexposed_middle_hidden_rank_band
      hp hcap htpos htone hlam hcard
      (show top ≠ b by simpa using hbTop)
      (C b) hbSup3 hbNotExp hbMiddle
  have hcBand :
      MiddleHiddenRankBand p top c :=
    nonexposed_middle_hidden_rank_band
      hp hcap htpos htone hlam hcard
      (show top ≠ c by simpa using hcTop)
      (C c) hcSup3 hcNotExp hcMiddle

  have hsame :
      (CanonicalPointLt p b top ∧ CanonicalPointLt p c top) ∨
      (CanonicalPointLt p top b ∧ CanonicalPointLt p top c) :=
    middleHiddenRankBand_same_side hbBand hcBand

  exact ⟨b,c,
    hbTop,hcTop,hbA,hcA,hbc,
    hbSup3,hcSup3,
    hbBand,hcBand,hsame⟩

#print axioms mixed_support_one_two_middle_hidden_rank_bands_same_side

end JSP000404Research
