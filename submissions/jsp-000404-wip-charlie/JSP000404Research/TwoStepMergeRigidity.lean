
import JSP000404Research.MergeZeroGain
import Mathlib.Tactic

/-!
# Two consecutive zero-gain deletions force a sparse quotient triple

Consider two adjacent ray deletions around three consecutive old quotient gaps

  a, b, c.

Deleting the first ray merges a and b into

  m = a+b+carry1.

If that merge has zero exponent gain, a and b cannot both be positive.

Now delete the adjacent second ray.  Its local merge uses m and c.  If this
second merge also has zero gain, m and c cannot both be positive.  Since
m >= a and m >= b, positivity of c forces a=b=0.

Hence among the original triple a,b,c at most one entry is positive.

This is the local arithmetic form needed when a minimal-overweight exact child
is subjected to a second minimum-centre deletion: SecondDeletionSlack forbids
a unit gain at every survivor above the minimum exponent layer, so adjacent
minimum rays force this three-gap sparsity.
-/

namespace JSP000404Research

/-- If the second zero-gain merge sees a positive final gap, both gaps consumed
by the first merge were zero. -/
theorem second_zero_gain_with_positive_tail_forces_first_pair_zero
    {rest₁ rest₂ a b c carry₁ carry₂ : ℕ}
    (hzero₁ :
      exponentAfterMerge rest₁ a b carry₁ =
        exponentBeforeMerge rest₁ a b)
    (hzero₂ :
      exponentAfterMerge rest₂ (a + b + carry₁) c carry₂ =
        exponentBeforeMerge rest₂ (a + b + carry₁) c)
    (hc : 1 ≤ c) :
    a = 0 ∧ b = 0 := by
  have hnot₂ :=
    zero_gain_not_both_pos hzero₂
  have hmzero :
      a + b + carry₁ = 0 := by
    by_contra hm
    have hmpos : 1 ≤ a + b + carry₁ := by omega
    exact hnot₂ ⟨hmpos, hc⟩
  omega

/-- Two consecutive zero-gain merges make the three original quotients
pairwise non-positive: no two of a,b,c can both be positive. -/
theorem two_step_zero_gain_triple_pairwise_sparse
    {rest₁ rest₂ a b c carry₁ carry₂ : ℕ}
    (hzero₁ :
      exponentAfterMerge rest₁ a b carry₁ =
        exponentBeforeMerge rest₁ a b)
    (hzero₂ :
      exponentAfterMerge rest₂ (a + b + carry₁) c carry₂ =
        exponentBeforeMerge rest₂ (a + b + carry₁) c) :
    ¬ (1 ≤ a ∧ 1 ≤ b) ∧
    ¬ (1 ≤ a ∧ 1 ≤ c) ∧
    ¬ (1 ≤ b ∧ 1 ≤ c) := by
  have hab :=
    zero_gain_not_both_pos hzero₁
  refine ⟨hab, ?_, ?_⟩
  · rintro ⟨ha, hc⟩
    have hmpos : 1 ≤ a + b + carry₁ := by omega
    exact
      (zero_gain_not_both_pos hzero₂)
        ⟨hmpos, hc⟩
  · rintro ⟨hb, hc⟩
    have hmpos : 1 ≤ a + b + carry₁ := by omega
    exact
      (zero_gain_not_both_pos hzero₂)
        ⟨hmpos, hc⟩

/-- Equivalent case split: one of the three gaps may be positive, but the
other two must be zero. -/
theorem two_step_zero_gain_triple_shape
    {rest₁ rest₂ a b c carry₁ carry₂ : ℕ}
    (hzero₁ :
      exponentAfterMerge rest₁ a b carry₁ =
        exponentBeforeMerge rest₁ a b)
    (hzero₂ :
      exponentAfterMerge rest₂ (a + b + carry₁) c carry₂ =
        exponentBeforeMerge rest₂ (a + b + carry₁) c) :
    (a = 0 ∧ b = 0) ∨
    (a = 0 ∧ c = 0) ∨
    (b = 0 ∧ c = 0) := by
  have hs :=
    two_step_zero_gain_triple_pairwise_sparse
      hzero₁ hzero₂
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · exact Or.inl ⟨ha, hb⟩
    · have hbpos : 1 ≤ b := by omega
      have hc0 : c = 0 := by
        by_contra hc
        exact hs.2.2 ⟨hbpos, by omega⟩
      exact Or.inr (Or.inl ⟨ha, hc0⟩)
  · have hapos : 1 ≤ a := by omega
    have hb0 : b = 0 := by
      by_contra hb
      exact hs.1 ⟨hapos, by omega⟩
    have hc0 : c = 0 := by
      by_contra hc
      exact hs.2.1 ⟨hapos, by omega⟩
    exact Or.inr (Or.inr ⟨hb0, hc0⟩)

#print axioms second_zero_gain_with_positive_tail_forces_first_pair_zero
#print axioms two_step_zero_gain_triple_pairwise_sparse
#print axioms two_step_zero_gain_triple_shape

end JSP000404Research
