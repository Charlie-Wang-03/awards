import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# One-dimensional interval counts behind the phase argument

Let a ray gap have normalized length x and contain b phase-partition
boundaries.  The nearest partition boundary before the gap and the nearest one
after the gap enclose it in a span made from b+1 consecutive partition
spacings.

For an ordinary span all these spacings have length one, hence

  x < b + 1  ->  floor x <= b.

If the span contains the unique long spacing of length 1+delta, then

  x < b + 1 + delta,

and delta < 1 gives only one possible lost boundary,

  floor x <= b + 1.

These are the real/floor arithmetic pieces of the one-exception boundary
domination.  The cyclic-order construction of the enclosing boundaries is
kept separate.
-/

namespace JSP000404Research

/-- An interval of nonnegative length strictly below b+1 has natural floor at
most b. -/
theorem natFloor_le_of_lt_count_succ
    {x : ℝ} {b : ℕ}
    (hx0 : 0 ≤ x)
    (hlt : x < (b : ℝ) + 1) :
    Nat.floor x ≤ b := by
  have hfloorlt : Nat.floor x < b + 1 := by
    exact (Nat.floor_lt hx0).2 (by
      norm_num at hlt ⊢
      exact hlt)
  omega

/-- If the enclosing span contains the unique extra slack delta<1, at most one
boundary can be lost relative to the natural floor. -/
theorem natFloor_le_count_add_one_of_lt_succ_add_delta
    {x delta : ℝ} {b : ℕ}
    (hx0 : 0 ≤ x)
    (hdelta : delta < 1)
    (hlt : x < (b : ℝ) + 1 + delta) :
    Nat.floor x ≤ b + 1 := by
  have hspan : x < ((b + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    linarith
  exact natFloor_le_of_lt_count_succ hx0 hspan

/-- Ordinary-span quotient domination in the form used by BoundaryDominance. -/
theorem quotient_le_boundary_count_of_ordinary_span
    {x : ℝ} {q b : ℕ}
    (hx0 : 0 ≤ x)
    (hq : q = Nat.floor x)
    (hspan : x < (b : ℝ) + 1) :
    q ≤ b := by
  subst q
  exact natFloor_le_of_lt_count_succ hx0 hspan

/-- Exceptional-span quotient domination: the unique long partition spacing
can cost at most one boundary. -/
theorem quotient_le_boundary_count_add_one_of_long_span
    {x delta : ℝ} {q b : ℕ}
    (hx0 : 0 ≤ x)
    (hq : q = Nat.floor x)
    (hdelta : delta < 1)
    (hspan : x < (b : ℝ) + 1 + delta) :
    q ≤ b + 1 := by
  subst q
  exact natFloor_le_count_add_one_of_lt_succ_add_delta
    hx0 hdelta hspan

#print axioms natFloor_le_of_lt_count_succ
#print axioms natFloor_le_count_add_one_of_lt_succ_add_delta
#print axioms quotient_le_boundary_count_of_ordinary_span
#print axioms quotient_le_boundary_count_add_one_of_long_span

end JSP000404Research
