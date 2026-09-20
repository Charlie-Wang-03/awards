import JSP000404Research.SupportTwoDeletion
import JSP000404Research.MergeCarry
import Mathlib.Tactic

/-!
# Stable separated support-two quotient profiles

The adjacent-positive branch of support=2 is already paid by deletion gain.
This file isolates the complementary regime.

For a displayed adjacent merge a,b:

* if not both a,b are positive;
* and the fractional merge carry is zero;

then the full Sendov list exponent is unchanged.

Moreover, if all fractional remainders are nonnegative and their total mass is
strictly below one, then every pair of remainders has zero binary carry.
In the lower-branch deficit-two/support-two case the total remainder is exactly
delta<1/2, so the no-carry hypothesis is automatic.

Therefore the genuinely deletion-stable support-two obstruction is precisely
the separated-positive regime: no deletion sees both positive quotient gaps at
once.
-/

namespace JSP000404Research

/-- With zero carry, a displayed adjacent merge is exponent-neutral whenever
the two old quotient entries are not both positive. -/
theorem listExponent_merge_eq_of_not_both_positive_no_carry
    (pre post : List ℕ) (a b : ℕ)
    (hnotboth : ¬ (1 ≤ a ∧ 1 ≤ b)) :
    listExponent
        (mergeDisplayedAdjacent pre a b 0 post)
      =
    listExponent (pre ++ a :: b :: post) := by
  rw [listExponent_displayed_pair,
      listExponent_merged_displayed_pair]
  by_cases ha : a = 0
  · subst a
    simp [excess]
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    have hb0 : b = 0 := by
      by_contra hb
      exact hnotboth ⟨ha1, Nat.one_le_iff_ne_zero.mpr hb⟩
    subst b
    simp [excess]

/-- A displayed adjacent pair which is not both positive and whose fractional
remainders do not carry is exponent-neutral. -/
theorem listExponent_merge_eq_of_stable_pair
    (pre post : List ℕ) (a b : ℕ)
    (r s : ℝ)
    (hnotboth : ¬ (1 ≤ a ∧ 1 ≤ b))
    (hrsum : r + s < 1) :
    listExponent
        (mergeDisplayedAdjacent pre a b (binaryCarry r s) post)
      =
    listExponent (pre ++ a :: b :: post) := by
  rw [binaryCarry_eq_zero_of_lt hrsum]
  exact listExponent_merge_eq_of_not_both_positive_no_carry
    pre post a b hnotboth

/-- Distinct-pair version used for adjacent cyclic gaps. -/
theorem distinct_pair_sum_lt_one_of_nonneg_total_lt_one
    {I : Type*} [Fintype I]
    (rem : I → ℝ)
    (hrem0 : ∀ i, 0 ≤ rem i)
    (htotal : (∑ i, rem i) < 1)
    {a b : I} (hab : a ≠ b) :
    rem a + rem b < 1 := by
  classical
  let S : Finset I := {a, b}
  have hS :
      ∑ i ∈ S, rem i = rem a + rem b := by
    simp [S, hab, add_comm]
  have hpair_le :
      rem a + rem b ≤ ∑ i, rem i := by
    rw [← hS]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ S)
      (fun i _ _ => hrem0 i)
  linarith

/-- Consequently every distinct pair has zero binary carry. -/
theorem binaryCarry_eq_zero_of_nonneg_total_lt_one
    {I : Type*} [Fintype I]
    (rem : I → ℝ)
    (hrem0 : ∀ i, 0 ≤ rem i)
    (htotal : (∑ i, rem i) < 1)
    {a b : I} (hab : a ≠ b) :
    binaryCarry (rem a) (rem b) = 0 := by
  apply binaryCarry_eq_zero_of_lt
  exact distinct_pair_sum_lt_one_of_nonneg_total_lt_one
    rem hrem0 htotal hab

/-- Lower-branch form: total remainder delta<1/2 certainly forbids every
distinct-gap carry. -/
theorem binaryCarry_eq_zero_of_remainder_sum_eq_delta
    {I : Type*} [Fintype I]
    (rem : I → ℝ)
    (hrem0 : ∀ i, 0 ≤ rem i)
    {delta : ℝ}
    (hsum : (∑ i, rem i) = delta)
    (hdelta : delta < (1 : ℝ) / 2)
    {a b : I} (hab : a ≠ b) :
    binaryCarry (rem a) (rem b) = 0 := by
  apply binaryCarry_eq_zero_of_nonneg_total_lt_one
    rem hrem0
  · rw [hsum]
    linarith
  · exact hab

/-- Abstract stable support-two conclusion for a displayed deletion: if the
displayed quotient pair is not both positive and the global remainder mass is
delta<1/2, the deletion is exponent-neutral. -/
theorem support_two_displayed_merge_neutral_of_separated
    {I : Type*} [Fintype I]
    (pre post : List ℕ) (a b : ℕ)
    (rem : I → ℝ)
    (hrem0 : ∀ i, 0 ≤ rem i)
    {delta : ℝ}
    (hsum : (∑ i, rem i) = delta)
    (hdelta : delta < (1 : ℝ) / 2)
    {ra rb : I} (hrab : ra ≠ rb)
    (hnotboth : ¬ (1 ≤ a ∧ 1 ≤ b)) :
    listExponent
        (mergeDisplayedAdjacent pre a b
          (binaryCarry (rem ra) (rem rb)) post)
      =
    listExponent (pre ++ a :: b :: post) := by
  apply listExponent_merge_eq_of_stable_pair
  · exact hnotboth
  · exact distinct_pair_sum_lt_one_of_nonneg_total_lt_one
      rem hrem0
      (by rw [hsum]; linarith)
      hrab

#print axioms listExponent_merge_eq_of_not_both_positive_no_carry
#print axioms distinct_pair_sum_lt_one_of_nonneg_total_lt_one
#print axioms binaryCarry_eq_zero_of_remainder_sum_eq_delta
#print axioms support_two_displayed_merge_neutral_of_separated

end JSP000404Research
