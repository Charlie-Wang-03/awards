import JSP000404Research.MergeGainCases
import Mathlib.Tactic

/-!
# Exact characterization of a zero-gain gap merge

For a surviving centre, deleting one ray merges two adjacent quotient gaps
a,b with binary carry c <= 1.

The local exponent gain is zero exactly in the following cases:

* c = 0 and at least one of a,b is zero;
* c = 1 and both a,b are zero.

Equivalently, zero gain forbids two adjacent positive quotients; moreover a
carry across a pair with positive total would force positive gain.

This is the local rigidity behind a centre whose exponent never increases
under deletion of any incident ray.
-/

namespace JSP000404Research

/-- Zero exponent gain forbids two positive merged quotients. -/
theorem zero_gain_not_both_pos
    {rest a b carry : ℕ}
    (hzero :
      exponentAfterMerge rest a b carry =
        exponentBeforeMerge rest a b) :
    ¬ (1 ≤ a ∧ 1 ≤ b) := by
  rintro ⟨ha, hb⟩
  have hgain :=
    exponent_merge_gain_of_both_pos
      (rest := rest) (a := a) (b := b) (carry := carry) ha hb
  omega

/-- If a binary carry occurs and the merge has zero gain, then both old
quotients must be zero. -/
theorem zero_gain_carry_one_imp_both_zero
    {rest a b carry : ℕ}
    (hc : carry = 1)
    (hzero :
      exponentAfterMerge rest a b carry =
        exponentBeforeMerge rest a b) :
    a = 0 ∧ b = 0 := by
  subst carry
  by_cases hab : a + b = 0
  · omega
  · have hpos : 1 ≤ a + b := by omega
    have hgain :=
      exponent_merge_gain_of_carry
        (rest := rest) (a := a) (b := b) (carry := 1)
        hpos (by omega)
    omega

/-- No-carry zero gain is equivalent to at least one zero quotient. -/
theorem zero_gain_no_carry_iff
    {rest a b : ℕ} :
    exponentAfterMerge rest a b 0 =
        exponentBeforeMerge rest a b ↔
      a = 0 ∨ b = 0 := by
  constructor
  · intro hzero
    by_contra h
    push_neg at h
    have ha : 1 ≤ a := by omega
    have hb : 1 ≤ b := by omega
    have hgain :=
      exponent_merge_gain_of_both_pos
        (rest := rest) (a := a) (b := b) (carry := 0) ha hb
    omega
  · intro hzero
    rcases hzero with rfl | rfl
    · exact exponent_merge_eq_of_zero_left rest b
    · exact exponent_merge_eq_of_zero_right rest a

/-- One-carry zero gain is equivalent to both quotients being zero. -/
theorem zero_gain_one_carry_iff
    {rest a b : ℕ} :
    exponentAfterMerge rest a b 1 =
        exponentBeforeMerge rest a b ↔
      a = 0 ∧ b = 0 := by
  constructor
  · intro hzero
    exact zero_gain_carry_one_imp_both_zero rfl hzero
  · rintro ⟨rfl, rfl⟩
    simp [exponentAfterMerge, exponentBeforeMerge, excess]

/-- Exact dichotomy for a binary carry. -/
theorem zero_gain_binary_iff
    {rest a b carry : ℕ}
    (hc : carry ≤ 1) :
    exponentAfterMerge rest a b carry =
        exponentBeforeMerge rest a b ↔
      (carry = 0 ∧ (a = 0 ∨ b = 0)) ∨
      (carry = 1 ∧ a = 0 ∧ b = 0) := by
  interval_cases carry
  · simp [zero_gain_no_carry_iff]
  · simp [zero_gain_one_carry_iff]

#print axioms zero_gain_not_both_pos
#print axioms zero_gain_carry_one_imp_both_zero
#print axioms zero_gain_no_carry_iff
#print axioms zero_gain_one_carry_iff
#print axioms zero_gain_binary_iff

end JSP000404Research
