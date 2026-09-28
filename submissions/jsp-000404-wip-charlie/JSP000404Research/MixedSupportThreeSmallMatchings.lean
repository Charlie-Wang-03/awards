import JSP000404Research.MixedSupportThreeNonExposed
import JSP000404Research.SixPointHardSupportReduction
import JSP000404Research.SupportThreeMiddleHiddenMatching
import Mathlib.Tactic

/-!
# Two small perfect matchings in the hard mixed branch

In the mixed six-point hard branch, fix a support-one minimum a.

The exposure budget forces two further minima b,c to be non-exposed
support-three centres.  If compensated minimum deletion is excluded, every
support-three centre is forced into the pinned middle-hidden shape.  Each such
shape supplies two disjoint non-top angular edges whose total angle is at most
delta*lambda.

Because there are exactly five minima, the four endpoints at each centre are
precisely all other minima.  Thus each centre carries a perfect matching on the
remaining four minima.

This packages the remaining mixed branch as a finite five-vertex matching
problem.
-/

namespace JSP000404Research

structure SmallPerfectMatchingAwayFromTop
    {V : Type*} {p : V → Plane}
    (top i : V) (delta lam : ℝ) where
  a : OtherVertex i
  b : OtherVertex i
  c : OtherVertex i
  d : OtherVertex i
  a_ne_top : a.1 ≠ top
  b_ne_top : b.1 ≠ top
  c_ne_top : c.1 ≠ top
  d_ne_top : d.1 ≠ top
  a_ne_b : a ≠ b
  a_ne_c : a ≠ c
  a_ne_d : a ≠ d
  b_ne_c : b ≠ c
  b_ne_d : b ≠ d
  c_ne_d : c ≠ d
  small_sum :
    EuclideanGeometry.angle (p a.1) (p i) (p b.1) +
      EuclideanGeometry.angle (p c.1) (p i) (p d.1)
      ≤ delta * lam

theorem support_three_middle_smallPerfectMatching
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : CentreProjectiveCycle hp i)
    {lam t delta : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {top i : V}
    (hit : i ≠ top)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3)
    (hmiddle :
      SupportThreePinnedMiddleShape hp
        (show top ≠ i by simpa using hit) C) :
    Nonempty
      (SmallPerfectMatchingAwayFromTop
        (p := p) top i delta lam) := by
  obtain ⟨a,b,c,d,
      hat,hbt,hct,hdt,
      hab,hac,had,hbc,hbd,hcd,
      hsmall⟩ :=
    support_three_middle_hidden_small_matching
      hp hcap C hcard hn hdelta0 hdeltaHalf
      ht hlam hit hexp hsupport hmiddle
  exact ⟨{
    a := a
    b := b
    c := c
    d := d
    a_ne_top := hat
    b_ne_top := hbt
    c_ne_top := hct
    d_ne_top := hdt
    a_ne_b := hab
    a_ne_c := hac
    a_ne_d := had
    b_ne_c := hbc
    b_ne_d := hbd
    c_ne_d := hcd
    small_sum := hsmall
  }⟩

/-- Mixed support-one hard branch: two distinct support-three minima each carry
a delta-small perfect matching on the other four minima. -/
theorem mixed_support_one_has_two_smallPerfectMatchings
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
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
        (SmallPerfectMatchingAwayFromTop
          (p := p) top b delta lam) ∧
      Nonempty
        (SmallPerfectMatchingAwayFromTop
          (p := p) top c delta lam) := by
  obtain ⟨b,c,
      hbTop,hcTop,hbA,hcA,hbc,
      hbSup3,hcSup3,
      _hbTrans,_hcTrans⟩ :=
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
  · exact support_three_middle_smallPerfectMatching
      hp hcap (C b) hcard (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      hbTop (hMin b hbTop) hbSup3 hbMiddle
  · exact support_three_middle_smallPerfectMatching
      hp hcap (C c) hcard (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      hcTop (hMin c hcTop) hcSup3 hcMiddle

#print axioms support_three_middle_smallPerfectMatching
#print axioms mixed_support_one_has_two_smallPerfectMatchings

end JSP000404Research
