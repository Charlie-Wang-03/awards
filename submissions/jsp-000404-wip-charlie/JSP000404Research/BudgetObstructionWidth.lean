import JSP000404Research.BoundaryFailureStructure
import Mathlib.Tactic

/-!
# Width of a local budget-failure obstruction

Suppose an exceptional ray gap has normalized length

  x = q + r,    0 <= r < 1.

At a bad phase, BoundaryFailureStructure gives q = b+1, where b is the
number of phase boundaries inside the gap.

The nearest partition boundaries surrounding the ray gap are then separated
by exactly q partition spacings.  Because this enclosing span contains the
unique long spacing, its length is q+delta.  Hence

  q+r = x < q+delta,

so necessarily r < delta.

The enclosing long-spacing window has slack delta-r, which lies in
(0,delta].  This is an upper envelope for where a one-boundary loss can occur;
the actual budget-bad phase set may be strictly smaller because boundary hits
in other gaps can compensate the lost floor excess.
-/

namespace JSP000404Research

/-- A one-boundary deficit inside the unique long span forces the fractional
remainder of the ray gap below delta. -/
theorem remainder_lt_delta_of_lost_boundary
    {x r delta : ℝ} {q b : ℕ}
    (hx : x = (q : ℝ) + r)
    (hqb : q = b + 1)
    (hspan : x < (b : ℝ) + 1 + delta) :
    r < delta := by
  subst q
  rw [hx] at hspan
  push_cast at hspan
  linarith

/-- The resulting budget-obstruction width delta-r is positive and at most
delta whenever r is nonnegative. -/
theorem budget_obstruction_width_bounds
    {r delta : ℝ}
    (hr0 : 0 ≤ r)
    (hrdelta : r < delta) :
    0 < delta - r ∧ delta - r ≤ delta := by
  constructor <;> linarith

/-- Non-strict version convenient for interval-length estimates. -/
theorem budget_obstruction_width_nonneg_le
    {r delta : ℝ}
    (hr0 : 0 ≤ r)
    (hrdelta : r ≤ delta) :
    0 ≤ delta - r ∧ delta - r ≤ delta := by
  constructor <;> linarith

#print axioms remainder_lt_delta_of_lost_boundary
#print axioms budget_obstruction_width_bounds
#print axioms budget_obstruction_width_nonneg_le

end JSP000404Research
