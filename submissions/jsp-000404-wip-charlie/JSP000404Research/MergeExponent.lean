import JSP000404Research.MergeGain
import Mathlib.Tactic

/-!
# Local exponent update under one gap merge

At a surviving centre, deleting one other ray merges exactly two adjacent gap
quotients. All other gap contributions to the Sendov exponent are unchanged.

If their old quotients are `a,b`, the merged quotient is `a+b+c` where the
carry `c` is 0 or 1. Writing the unchanged contribution as `rest`, the old
and new centre exponents are

  rest + excess a + excess b
  rest + excess (a+b+c).

The following lemmas lift the pointwise `MergeGain` arithmetic to the whole
centre exponent.
-/

namespace JSP000404Research

/-- Exponent before merging the two distinguished adjacent gaps. -/
def exponentBeforeMerge (rest a b : ℕ) : ℕ :=
  rest + excess a + excess b

/-- Exponent after merging the distinguished adjacent gaps. -/
def exponentAfterMerge (rest a b carry : ℕ) : ℕ :=
  rest + excess (a + b + carry)

/-- Deleting a ray cannot decrease the surviving centre's exponent. -/
theorem exponent_merge_mono
    (rest a b carry : ℕ) :
    exponentBeforeMerge rest a b ≤
      exponentAfterMerge rest a b carry := by
  unfold exponentBeforeMerge exponentAfterMerge
  have h := excess_merge_mono a b carry
  omega

/-- If both adjacent old quotients are positive, deletion raises the full
centre exponent by at least one. -/
theorem exponent_merge_gain_of_both_pos
    {rest a b carry : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    exponentBeforeMerge rest a b + 1 ≤
      exponentAfterMerge rest a b carry := by
  unfold exponentBeforeMerge exponentAfterMerge
  have h := excess_merge_gain_of_both_pos (c := carry) ha hb
  omega

/-- If the merge creates a carry and at least one old quotient is positive,
the full centre exponent rises by at least one. -/
theorem exponent_merge_gain_of_carry
    {rest a b carry : ℕ}
    (hab : 1 ≤ a + b) (hc : 1 ≤ carry) :
    exponentBeforeMerge rest a b + 1 ≤
      exponentAfterMerge rest a b carry := by
  unfold exponentBeforeMerge exponentAfterMerge
  have h := excess_merge_gain_of_carry hab hc
  omega

/-- With binary carry, a single gap merge raises the full exponent by at most
two. -/
theorem exponent_merge_gain_le_two
    {rest a b carry : ℕ}
    (hc : carry ≤ 1) :
    exponentAfterMerge rest a b carry ≤
      exponentBeforeMerge rest a b + 2 := by
  unfold exponentBeforeMerge exponentAfterMerge
  have h := excess_merge_gain_le_two (a := a) (b := b) hc
  omega

/-- With no carry and only one positive side, the full exponent is unchanged. -/
theorem exponent_merge_eq_of_zero_left
    (rest b : ℕ) :
    exponentAfterMerge rest 0 b 0 =
      exponentBeforeMerge rest 0 b := by
  simp [exponentAfterMerge, exponentBeforeMerge,
    excess_merge_eq_of_zero_left]

theorem exponent_merge_eq_of_zero_right
    (rest a : ℕ) :
    exponentAfterMerge rest a 0 0 =
      exponentBeforeMerge rest a 0 := by
  simp [exponentAfterMerge, exponentBeforeMerge,
    excess_merge_eq_of_zero_right]

#print axioms exponent_merge_mono
#print axioms exponent_merge_gain_of_both_pos
#print axioms exponent_merge_gain_of_carry
#print axioms exponent_merge_gain_le_two
#print axioms exponent_merge_eq_of_zero_left
#print axioms exponent_merge_eq_of_zero_right

end JSP000404Research
