import JSP000404Research.PhaseArithmetic
import Mathlib.Tactic

/-!
# Abstract phase-obstruction reduction

The lower Sendov branch has now been reduced to a rotating-phase problem.
Let the phase circle have normalized circumference n+delta, with
0 <= delta < 1/2.

The remaining geometry is expected to provide finitely many obstruction
intervals, each of length at most delta.  If every phase were bad, these
intervals would cover the whole phase circle, hence

  n + delta <= m * delta

where m is the number of obstruction intervals.

On the other hand the obstructions are intended to inject into the vertices
(or edges) of the least convex polygon.  The global angle cap gives the
hull-count estimate

  h <= 2 * (n + delta).

Since h is an integer and delta < 1/2, PhaseArithmetic already yields h <= 2n.
But any delta-cover of a circle of length n+delta needs at least 2n+2
intervals.  Therefore not every phase can be bad.

This module formalizes exactly that final arithmetic/reductive shell.  It does
not assume or hide the geometric construction of obstruction intervals.
-/

namespace JSP000404Research

/-- If "all phases are bad" would force a delta-cover using at most 2n
obstructions, then a good phase exists. -/
theorem exists_good_phase_of_bad_cover_count
    {Phase : Type*} [Nonempty Phase]
    (Bad : Phase → Prop)
    {n m : ℕ} {delta : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hm : m ≤ 2 * n)
    (hallbad_cover :
      (∀ phase, Bad phase) →
        (n : ℝ) + delta ≤ (m : ℝ) * delta) :
    ∃ phase, ¬ Bad phase := by
  by_contra hgood
  push_neg at hgood
  have hcover := hallbad_cover hgood
  have hlower :=
    phase_cover_count_lower hn hdelta0 hdelta hcover
  omega

/-- Hull-count form of the same reduction.

The geometric side may naturally produce an obstruction count m bounded by
a hull count h, together with h <= 2(n+delta).  The integer rounding theorem
in PhaseArithmetic then supplies m <= 2n automatically. -/
theorem exists_good_phase_of_bad_cover_hull
    {Phase : Type*} [Nonempty Phase]
    (Bad : Phase → Prop)
    {n m h : ℕ} {delta : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hmh : m ≤ h)
    (hhull : (h : ℝ) ≤ 2 * ((n : ℝ) + delta))
    (hallbad_cover :
      (∀ phase, Bad phase) →
        (n : ℝ) + delta ≤ (m : ℝ) * delta) :
    ∃ phase, ¬ Bad phase := by
  by_contra hgood
  push_neg at hgood
  exact phase_cover_hull_count_contradiction
    hn hdelta0 hdelta
    (hallbad_cover hgood) hhull hmh

/-- Contrapositive certificate: if at most h obstruction intervals exist and
h satisfies the convex-hull bound, those intervals cannot cover the full
phase circle. -/
theorem obstruction_cover_impossible_of_hull_bound
    {n m h : ℕ} {delta : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hmh : m ≤ h)
    (hhull : (h : ℝ) ≤ 2 * ((n : ℝ) + delta)) :
    ¬ ((n : ℝ) + delta ≤ (m : ℝ) * delta) := by
  intro hcover
  exact phase_cover_hull_count_contradiction
    hn hdelta0 hdelta hcover hhull hmh

#print axioms exists_good_phase_of_bad_cover_count
#print axioms exists_good_phase_of_bad_cover_hull
#print axioms obstruction_cover_impossible_of_hull_bound

end JSP000404Research
