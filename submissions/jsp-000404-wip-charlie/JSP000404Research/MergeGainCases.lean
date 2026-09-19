import JSP000404Research.MergeExponent
import JSP000404Research.MergeCarry
import Mathlib.Tactic

/-!
# Exact cases of the local gap-merge gain

For a surviving centre, deleting one ray merges two adjacent quotient gaps
`a,b` with binary carry `c <= 1`.

The exponent gain is completely explicit:

* a=b=0: gain 0;
* exactly one of a,b is positive: gain c;
* both a,b are positive: gain 1+c.

Thus the dyadic weight bonus is respectively 0, 0 or one old weight in the
no-carry case, and one or three old weights when a carry occurs.
-/

namespace JSP000404Research

/-- Two zero quotients give no exponent gain for a binary carry. -/
theorem exponent_merge_eq_of_both_zero
    {rest carry : ℕ} (hc : carry ≤ 1) :
    exponentAfterMerge rest 0 0 carry =
      exponentBeforeMerge rest 0 0 := by
  unfold exponentAfterMerge exponentBeforeMerge excess
  omega

/-- If only the right quotient is positive, the exponent gain equals the
binary carry. -/
theorem exponent_merge_eq_of_left_zero
    {rest b carry : ℕ}
    (hb : 1 ≤ b) (hc : carry ≤ 1) :
    exponentAfterMerge rest 0 b carry =
      exponentBeforeMerge rest 0 b + carry := by
  unfold exponentAfterMerge exponentBeforeMerge excess
  omega

/-- Symmetric one-positive case. -/
theorem exponent_merge_eq_of_right_zero
    {rest a carry : ℕ}
    (ha : 1 ≤ a) (hc : carry ≤ 1) :
    exponentAfterMerge rest a 0 carry =
      exponentBeforeMerge rest a 0 + carry := by
  unfold exponentAfterMerge exponentBeforeMerge excess
  omega

/-- If both old quotients are positive, the gain is exactly one plus the
binary carry. -/
theorem exponent_merge_eq_of_both_pos
    {rest a b carry : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : carry ≤ 1) :
    exponentAfterMerge rest a b carry =
      exponentBeforeMerge rest a b + 1 + carry := by
  unfold exponentAfterMerge exponentBeforeMerge excess
  omega

/-- One exponent unit doubles a dyadic weight, so the new-minus-old bonus is
exactly one old weight. -/
theorem pow_bonus_of_gain_one
    {old new : ℕ} (h : new = old + 1) :
    2 ^ new = 2 ^ old + 2 ^ old := by
  subst new
  rw [pow_succ]
  omega

/-- Two exponent units multiply a dyadic weight by four, hence produce a bonus
of three old weights. -/
theorem pow_bonus_of_gain_two
    {old new : ℕ} (h : new = old + 2) :
    2 ^ new = 2 ^ old + 3 * 2 ^ old := by
  subst new
  rw [show old + 2 = (old + 1) + 1 by omega, pow_succ, pow_succ]
  ring

/-- Both-positive/no-carry merge produces exactly one old-weight bonus. -/
theorem dyadic_merge_bonus_both_pos_no_carry
    {rest a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2 ^ exponentAfterMerge rest a b 0 =
      2 ^ exponentBeforeMerge rest a b +
        2 ^ exponentBeforeMerge rest a b := by
  apply pow_bonus_of_gain_one
  simpa using exponent_merge_eq_of_both_pos (rest := rest)
    (a := a) (b := b) (carry := 0) ha hb (by omega)

/-- Both-positive/one-carry merge produces exactly three old-weight bonuses. -/
theorem dyadic_merge_bonus_both_pos_carry
    {rest a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2 ^ exponentAfterMerge rest a b 1 =
      2 ^ exponentBeforeMerge rest a b +
        3 * 2 ^ exponentBeforeMerge rest a b := by
  apply pow_bonus_of_gain_two
  have h := exponent_merge_eq_of_both_pos (rest := rest)
    (a := a) (b := b) (carry := 1) ha hb (by omega)
  omega

/-- One-positive/one-carry merge produces exactly one old-weight bonus. -/
theorem dyadic_merge_bonus_one_pos_carry_left
    {rest b : ℕ} (hb : 1 ≤ b) :
    2 ^ exponentAfterMerge rest 0 b 1 =
      2 ^ exponentBeforeMerge rest 0 b +
        2 ^ exponentBeforeMerge rest 0 b := by
  apply pow_bonus_of_gain_one
  simpa using exponent_merge_eq_of_left_zero (rest := rest)
    (b := b) (carry := 1) hb (by omega)

/-- Symmetric one-positive/one-carry case. -/
theorem dyadic_merge_bonus_one_pos_carry_right
    {rest a : ℕ} (ha : 1 ≤ a) :
    2 ^ exponentAfterMerge rest a 0 1 =
      2 ^ exponentBeforeMerge rest a 0 +
        2 ^ exponentBeforeMerge rest a 0 := by
  apply pow_bonus_of_gain_one
  simpa using exponent_merge_eq_of_right_zero (rest := rest)
    (a := a) (carry := 1) ha (by omega)

#print axioms exponent_merge_eq_of_both_zero
#print axioms exponent_merge_eq_of_left_zero
#print axioms exponent_merge_eq_of_right_zero
#print axioms exponent_merge_eq_of_both_pos
#print axioms pow_bonus_of_gain_one
#print axioms pow_bonus_of_gain_two
#print axioms dyadic_merge_bonus_both_pos_no_carry
#print axioms dyadic_merge_bonus_both_pos_carry
#print axioms dyadic_merge_bonus_one_pos_carry_left
#print axioms dyadic_merge_bonus_one_pos_carry_right

end JSP000404Research
