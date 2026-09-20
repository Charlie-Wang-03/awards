import JSP000404Research.TriangleGapTransfer
import JSP000404Research.ShortArcTransition
import Mathlib.Tactic

/-!
# Recursive width reduction after support-two triangle transfer

For a deficit-two/support-two centre, let the two positive quotient masses be
a and b.  Their sum is n.

If the hidden same-sign gap with quotient b transfers to an opposite-sign
projective interval of normalized length s at a neighbouring centre, then

  b <= t*s.

Since t=n+delta and a+b=n, the complementary normalized arc has scaled width

  t*(1-s) <= a+delta.

Thus a large hidden quotient becomes a short complementary arc whose complexity
is controlled by the *other* quotient a.

In the hardest case a=1 and delta<1/2, the complement has scaled width <3/2,
hence certainly <2.  Because the complementary lifted endpoints have the same
sign, ShortArcTransition then forces zero sign transitions on that complement
once the actual ray-subarc extraction is supplied.
-/

namespace JSP000404Research

/-- Pure arithmetic complement-width reduction. -/
theorem support_two_transfer_complement_width
    {a b n : ℕ} {delta t s : ℝ}
    (ht : t = (n : ℝ) + delta)
    (hsum : a + b = n)
    (hs : 0 ≤ s)
    (hq : (b : ℝ) ≤ t * s) :
    t * (1 - s) ≤ (a : ℝ) + delta := by
  have hbn : (b : ℝ) = (n : ℝ) - (a : ℝ) := by
    exact_mod_cast (by omega : b = n - a)
  rw [ht] at hq ⊢
  rw [hbn] at hq
  nlinarith

/-- Unit transition quotient gives a complement shorter than 3/2 scaled units
in the lower branch. -/
theorem support_two_unit_transition_complement_lt_three_halves
    {b n : ℕ} {delta t s : ℝ}
    (ht : t = (n : ℝ) + delta)
    (hsum : 1 + b = n)
    (hdelta : delta < (1 : ℝ) / 2)
    (hs : 0 ≤ s)
    (hq : (b : ℝ) ≤ t * s) :
    t * (1 - s) < (3 : ℝ) / 2 := by
  have h :=
    support_two_transfer_complement_width
      (a := 1) (b := b) (n := n)
      (delta := delta) (t := t) (s := s)
      ht hsum hs hq
  norm_num at h ⊢
  linarith

/-- In particular the complement is below the two-unit transition threshold. -/
theorem support_two_unit_transition_complement_lt_two
    {b n : ℕ} {delta t s : ℝ}
    (ht : t = (n : ℝ) + delta)
    (hsum : 1 + b = n)
    (hdelta : delta < (1 : ℝ) / 2)
    (hs : 0 ≤ s)
    (hq : (b : ℝ) ≤ t * s) :
    t * (1 - s) < 2 := by
  have h :=
    support_two_unit_transition_complement_lt_three_halves
      ht hsum hdelta hs hq
  linarith

/-- Abstract Bool-path outlet for the transferred complement.  Geometry only
has to identify a complement path whose total scaled gap length is bounded by
the arithmetic complement above and whose endpoints agree after lifting. -/
theorem transferred_unit_complement_has_no_transition
    (a0 : Bool) (signs : List Bool) (scaledGaps : List ℝ)
    {b n : ℕ} {delta t s : ℝ}
    (ht : t = (n : ℝ) + delta)
    (hsum : 1 + b = n)
    (hdelta : delta < (1 : ℝ) / 2)
    (hs : 0 ≤ s)
    (hq : (b : ℝ) ≤ t * s)
    (hgapRule : TransitionGapLowerBound a0 signs scaledGaps)
    (hlast : boolLastFrom a0 signs = a0)
    (hlen : scaledGaps.sum ≤ t * (1 - s)) :
    boolTransitionCountFrom a0 signs = 0 := by
  apply zero_transition_of_short_same_arc
      a0 signs scaledGaps hgapRule hlast
  have hcomp :=
    support_two_unit_transition_complement_lt_two
      ht hsum hdelta hs hq
  exact hlen.trans_lt hcomp

#print axioms support_two_transfer_complement_width
#print axioms support_two_unit_transition_complement_lt_three_halves
#print axioms transferred_unit_complement_has_no_transition

end JSP000404Research
