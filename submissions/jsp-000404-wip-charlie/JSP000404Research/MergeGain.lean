import Mathlib.Tactic

/-!
# Compensated deletion: local merge gain

Deleting one top-level centre merges two adjacent angular gaps at every other
centre.  At the quotient level, if the two old integer parts are `a,b` and
the two fractional remainders create a carry `c in {0,1}`, the new quotient
is `a+b+c`.

The Sendov exponent uses the positive part `g(q)=(q-1)_+`.  The lemmas below
record the exact monotonicity needed by a compensated-deletion induction.
-/

namespace JSP000404Research

/-- Pointwise contribution to the Sendov exponent. -/
def excess (q : ℕ) : ℕ := q - 1

/-- Merging two quotient gaps can never decrease their total exponent
contribution, regardless of a nonnegative carry. -/
theorem excess_merge_mono (a b c : ℕ) :
    excess a + excess b ≤ excess (a + b + c) := by
  unfold excess
  omega

/-- If both merged gaps already have positive integer quotient, deleting their
common ray raises the local exponent contribution by at least one. -/
theorem excess_merge_gain_of_both_pos
    {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    excess a + excess b + 1 ≤ excess (a + b + c) := by
  unfold excess
  omega

/-- A carry also raises the contribution by at least one provided at least one
of the two old gaps already had positive quotient. -/
theorem excess_merge_gain_of_carry
    {a b c : ℕ} (hab : 1 ≤ a + b) (hc : 1 ≤ c) :
    excess a + excess b + 1 ≤ excess (a + b + c) := by
  unfold excess
  omega

/-- With a binary carry, the gain is at most two. -/
theorem excess_merge_gain_le_two
    {a b c : ℕ} (hc : c ≤ 1) :
    excess (a + b + c) ≤ excess a + excess b + 2 := by
  unfold excess
  omega

/-- If there is no carry and one side has zero quotient, merging is exactly
neutral. -/
theorem excess_merge_eq_of_zero_left
    {b : ℕ} :
    excess (0 + b + 0) = excess 0 + excess b := by
  simp [excess]

theorem excess_merge_eq_of_zero_right
    {a : ℕ} :
    excess (a + 0 + 0) = excess a + excess 0 := by
  simp [excess]

/-- If both old quotients are positive and there is no carry, the gain is
exactly one. -/
theorem excess_merge_eq_of_both_pos_no_carry
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    excess (a + b) = excess a + excess b + 1 := by
  unfold excess
  omega

/-- If both old quotients are positive and there is one carry, the gain is
exactly two. -/
theorem excess_merge_eq_of_both_pos_carry
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    excess (a + b + 1) = excess a + excess b + 2 := by
  unfold excess
  omega

#print axioms excess_merge_mono
#print axioms excess_merge_gain_of_both_pos
#print axioms excess_merge_gain_of_carry
#print axioms excess_merge_gain_le_two
#print axioms excess_merge_eq_of_both_pos_no_carry
#print axioms excess_merge_eq_of_both_pos_carry

end JSP000404Research
