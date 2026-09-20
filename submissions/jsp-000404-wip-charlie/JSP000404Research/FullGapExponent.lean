import JSP000404Research.FullBoundaryCount
import JSP000404Research.BoundaryIntervalCount
import Mathlib.Tactic

/-!
# Full boundary interlacing forces zero Sendov exponent

For the rotating (n+1)-boundary partition in the lower branch, every
consecutive boundary spacing is at most one normalized unit (n spacings are
one and the unique wrap spacing is delta < 1).

If a vertex is full, every radial gap contains at most one partition boundary.
For a generic phase, a radial gap containing b boundaries is strictly shorter
than the enclosing span of b+1 boundary spacings. Hence when b <= 1,

  gap length < b+1 <= 2,

so its natural quotient floor(gap length) is at most one.

Consequently every quotient coordinate is at most one and the Sendov
floor-excess exponent is zero.

The geometric statement producing the enclosing-span inequality is deliberately
kept as an input; this file closes the arithmetic implication.
-/

namespace JSP000404Research

open scoped BigOperators

/-- A gap with at most one internal boundary, enclosed by b+1 unit-or-shorter
boundary spacings, has quotient at most one. -/
theorem quotient_le_one_of_full_gap
    {x : ℝ} {q b : ℕ}
    (hx0 : 0 ≤ x)
    (hq : q = Nat.floor x)
    (hb : b ≤ 1)
    (hspan : x < (b : ℝ) + 1) :
    q ≤ 1 := by
  have hqb :
      q ≤ b := by
    subst q
    exact natFloor_le_of_lt_count_succ hx0 hspan
  omega

/-- Pointwise full-gap enclosure implies every quotient coordinate is at most
one. -/
theorem all_quotients_le_one_of_full_boundary_counts
    {I : Type*} [Fintype I]
    (x : I → ℝ) (q b : I → ℕ)
    (hx0 : ∀ i, 0 ≤ x i)
    (hq : ∀ i, q i = Nat.floor (x i))
    (hb : ∀ i, b i ≤ 1)
    (hspan : ∀ i, x i < (b i : ℝ) + 1) :
    ∀ i, q i ≤ 1 := by
  intro i
  exact quotient_le_one_of_full_gap
    (hx0 i) (hq i) (hb i) (hspan i)

/-- Therefore a full generic boundary interlacing has zero floor-excess. -/
theorem floorExcess_eq_zero_of_full_boundary_counts
    {I : Type*} [Fintype I]
    (x : I → ℝ) (q b : I → ℕ)
    (hx0 : ∀ i, 0 ≤ x i)
    (hq : ∀ i, q i = Nat.floor (x i))
    (hb : ∀ i, b i ≤ 1)
    (hspan : ∀ i, x i < (b i : ℝ) + 1) :
    floorExcess q = 0 := by
  apply (floorExcess_eq_zero_iff_all_le_one q).2
  exact all_quotients_le_one_of_full_boundary_counts
    x q b hx0 hq hb hspan

/-- Full occupancy plus total boundary mass gives the same conclusion through
the interlacing criterion. -/
theorem floorExcess_eq_zero_of_full_support
    {I : Type*} [Fintype I]
    (x : I → ℝ) (q b : I → ℕ) (k : ℕ)
    (hx0 : ∀ i, 0 ≤ x i)
    (hq : ∀ i, q i = Nat.floor (x i))
    (hsum : (∑ i, b i) = k)
    (hfull : positiveSupport b = k)
    (hspan : ∀ i, x i < (b i : ℝ) + 1) :
    floorExcess q = 0 := by
  have hb :=
    (positiveSupport_eq_total_iff_all_le_one b k hsum).1 hfull
  exact floorExcess_eq_zero_of_full_boundary_counts
    x q b hx0 hq hb hspan

#print axioms quotient_le_one_of_full_gap
#print axioms all_quotients_le_one_of_full_boundary_counts
#print axioms floorExcess_eq_zero_of_full_boundary_counts
#print axioms floorExcess_eq_zero_of_full_support

end JSP000404Research
