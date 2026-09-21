import Mathlib.Tactic

/-!
# Mixed four-centre interior arithmetic contradiction

This file isolates the linear arithmetic behind the remaining mixed
four-centre sharp case.

Suppose three high-exponent centres s,a,b form the outer triangle and the
fourth point lies inside it.  Write xs,xa,xb for their normalized transition
gap widths.  Then the three exterior turns add to two full projective
half-turns:

  xs + xa + xb = 2*t.

At the sharp centre s, an interior sub-angle p is at most t-xs.
At the support-one centre a, the two interior sub-angles u,v satisfy

  u+v = t-xa.

At the support-two centre b, the hidden positive quotient n-1 implies the
small zero-gap angle z satisfies

  z <= 1+delta-xb.

Finally the global angle cap on triangles s-a-c and a-b-c gives

  p+u >= 1,
  z+v >= 1.

Adding the last two inequalities gives a lower bound 2, while the first three
relations give the strict upper bound 1+delta<2.

The theorem below deliberately contains no geometry; it is the terminal
arithmetic outlet for the mixed interior case.
-/

namespace JSP000404Research

theorem mixed_four_interior_arithmetic_contradiction
    {t delta xs xa xb p u v z : ℝ}
    (hdelta : delta < 1)
    (hturn : xs + xa + xb = 2 * t)
    (hp : p ≤ t - xs)
    (huv : u + v = t - xa)
    (hz : z ≤ 1 + delta - xb)
    (hpu : 1 ≤ p + u)
    (hzv : 1 ≤ z + v) :
    False := by
  have hlower : 2 ≤ p + z + (u + v) := by
    linarith
  have hupper :
      p + z + (u + v) ≤ 1 + delta := by
    rw [huv]
    linarith [hturn]
  linarith

/-- Slightly weakened form: exact turn equality may be replaced by the lower
bound xs+xa+xb >= 2*t. -/
theorem mixed_four_interior_arithmetic_contradiction_of_turn_lower
    {t delta xs xa xb p u v z : ℝ}
    (hdelta : delta < 1)
    (hturn : 2 * t ≤ xs + xa + xb)
    (hp : p ≤ t - xs)
    (huv : u + v ≤ t - xa)
    (hz : z ≤ 1 + delta - xb)
    (hpu : 1 ≤ p + u)
    (hzv : 1 ≤ z + v) :
    False := by
  have hlower : 2 ≤ p + z + (u + v) := by
    linarith
  have hupper :
      p + z + (u + v) ≤ 1 + delta := by
    linarith
  linarith

#print axioms mixed_four_interior_arithmetic_contradiction
#print axioms mixed_four_interior_arithmetic_contradiction_of_turn_lower

end JSP000404Research
