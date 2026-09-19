import JSP000404Research.MergeZeroGain
import JSP000404Research.MergeCarry
import Mathlib.Tactic

/-!
# Fractional rigidity of a zero-gain merge

Write two adjacent normalized gaps as

  x = a + r,   y = b + s,

with natural quotients a,b and fractional remainders 0 <= r,s < 1.
Their merged quotient is a+b+binaryCarry r s.

If deleting the common ray produces zero exponent gain, then:

* a and b cannot both be positive;
* whenever a+b is positive, the binary carry must be zero;
* hence r+s < 1.

Thus an all-zero-gain centre has not only independent positive quotient
support, but also a strict fractional-sum constraint across every adjacency
touching that support.
-/

namespace JSP000404Research

/-- A zero-gain merge touching a positive quotient cannot carry. -/
theorem zero_gain_positive_sum_imp_carry_zero
    {rest a b : ℕ} {r s : ℝ}
    (hpos : 1 ≤ a + b)
    (hzero :
      exponentAfterMerge rest a b (binaryCarry r s) =
        exponentBeforeMerge rest a b) :
    binaryCarry r s = 0 := by
  have hc := binaryCarry_le_one r s
  interval_cases hcarry : binaryCarry r s
  · rfl
  · have hgain :=
      exponent_merge_gain_of_carry
        (rest := rest) (a := a) (b := b)
        (carry := binaryCarry r s) hpos (by omega)
    omega

/-- Therefore the two adjacent fractional remainders sum to less than one. -/
theorem zero_gain_positive_sum_imp_remainder_sum_lt_one
    {rest a b : ℕ} {r s : ℝ}
    (hpos : 1 ≤ a + b)
    (hzero :
      exponentAfterMerge rest a b (binaryCarry r s) =
        exponentBeforeMerge rest a b) :
    r + s < 1 := by
  have hc :=
    zero_gain_positive_sum_imp_carry_zero
      (rest := rest) (a := a) (b := b) (r := r) (s := s)
      hpos hzero
  by_contra hnot
  have hge : 1 ≤ r + s := le_of_not_gt hnot
  have hone := binaryCarry_eq_one_of_ge hge
  omega

/-- Combined local rigidity of a zero-gain merge. -/
theorem zero_gain_local_rigidity
    {rest a b : ℕ} {r s : ℝ}
    (hzero :
      exponentAfterMerge rest a b (binaryCarry r s) =
        exponentBeforeMerge rest a b) :
    ¬ (1 ≤ a ∧ 1 ≤ b) ∧
      (1 ≤ a + b → r + s < 1) := by
  constructor
  · exact zero_gain_not_both_pos hzero
  · intro hpos
    exact zero_gain_positive_sum_imp_remainder_sum_lt_one hpos hzero

#print axioms zero_gain_positive_sum_imp_carry_zero
#print axioms zero_gain_positive_sum_imp_remainder_sum_lt_one
#print axioms zero_gain_local_rigidity

end JSP000404Research
