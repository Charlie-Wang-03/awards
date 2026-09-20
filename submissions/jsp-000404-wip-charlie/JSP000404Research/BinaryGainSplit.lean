import Mathlib.Tactic

/-!
# Binary gain-split induction for Sendov dyadic weights

Single-centre compensated deletion is too strong and has an exact-numerical
hard stop.  A weaker recursive mechanism is sufficient.

Suppose a current finite centre set S is partitioned into two disjoint
children A and B.  When the opposite child is removed, every survivor gains at
least one Sendov exponent unit:

  k_A(v) >= k_S(v)+1  for v in A,
  k_B(v) >= k_S(v)+1  for v in B.

If each child configuration already satisfies the ordinary dyadic capacity

  sum_A 2^(k_A(v)) <= 2^n,
  sum_B 2^(k_B(v)) <= 2^n,

then each parent's half contributes at most 2^(n-1), so the parent satisfies

  sum_S 2^(k_S(v)) <= 2^n.

This is the arithmetic engine behind a recursive binary split tree and explains
why balanced Kraft profiles can close cases where no single compensated
deletion exists.
-/

namespace JSP000404Research

open scoped BigOperators

/-- One exponent gain doubles dyadic weight. -/
theorem doubled_old_weight_le_new_of_gain
    {old new : ℕ}
    (hgain : old + 1 ≤ new) :
    2 * 2 ^ old ≤ 2 ^ new := by
  have hpow :=
    Nat.pow_le_pow_right
      (by norm_num : 0 < 2) hgain
  rw [pow_succ] at hpow
  simpa [Nat.mul_comm] using hpow

/-- Summed form on one child. -/
theorem doubled_sum_le_post_sum_of_pointwise_gain
    {V : Type*}
    (A : Finset V)
    (old post : V → ℕ)
    (hgain : ∀ v ∈ A, old v + 1 ≤ post v) :
    2 * (∑ v ∈ A, 2 ^ old v) ≤
      ∑ v ∈ A, 2 ^ post v := by
  have hpoint :
      ∑ v ∈ A, 2 * 2 ^ old v ≤
        ∑ v ∈ A, 2 ^ post v :=
    Finset.sum_le_sum fun v hv =>
      doubled_old_weight_le_new_of_gain (hgain v hv)
  rw [← Finset.mul_sum] at hpoint
  exact hpoint

/-- Main binary split induction step. -/
theorem binary_gain_split_capacity_step
    {V : Type*}
    (S A B : Finset V)
    (old postA postB : V → ℕ)
    (n : ℕ)
    (hdisj : Disjoint A B)
    (hunion : S = A ∪ B)
    (hgainA : ∀ v ∈ A, old v + 1 ≤ postA v)
    (hgainB : ∀ v ∈ B, old v + 1 ≤ postB v)
    (hcapA : (∑ v ∈ A, 2 ^ postA v) ≤ 2 ^ n)
    (hcapB : (∑ v ∈ B, 2 ^ postB v) ≤ 2 ^ n) :
    (∑ v ∈ S, 2 ^ old v) ≤ 2 ^ n := by
  have hA :
      2 * (∑ v ∈ A, 2 ^ old v) ≤ 2 ^ n :=
    (doubled_sum_le_post_sum_of_pointwise_gain
      A old postA hgainA).trans hcapA
  have hB :
      2 * (∑ v ∈ B, 2 ^ old v) ≤ 2 ^ n :=
    (doubled_sum_le_post_sum_of_pointwise_gain
      B old postB hgainB).trans hcapB
  have hsum :
      2 * ((∑ v ∈ A, 2 ^ old v) +
        (∑ v ∈ B, 2 ^ old v)) ≤
      2 * 2 ^ n := by
    nlinarith
  have hparent :
      (∑ v ∈ S, 2 ^ old v) =
        (∑ v ∈ A, 2 ^ old v) +
        (∑ v ∈ B, 2 ^ old v) := by
    rw [hunion, Finset.sum_union hdisj]
  rw [hparent]
  omega

/-- Fintype specialization for a full parent split. -/
theorem binary_gain_split_fintype_capacity
    {V : Type*} [Fintype V]
    (A B : Finset V)
    (old postA postB : V → ℕ)
    (n : ℕ)
    (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ)
    (hgainA : ∀ v ∈ A, old v + 1 ≤ postA v)
    (hgainB : ∀ v ∈ B, old v + 1 ≤ postB v)
    (hcapA : (∑ v ∈ A, 2 ^ postA v) ≤ 2 ^ n)
    (hcapB : (∑ v ∈ B, 2 ^ postB v) ≤ 2 ^ n) :
    (∑ v : V, 2 ^ old v) ≤ 2 ^ n := by
  apply binary_gain_split_capacity_step
    Finset.univ A B old postA postB n hdisj
  · exact hcover.symm
  · exact hgainA
  · exact hgainB
  · exact hcapA
  · exact hcapB

#print axioms doubled_old_weight_le_new_of_gain
#print axioms doubled_sum_le_post_sum_of_pointwise_gain
#print axioms binary_gain_split_capacity_step
#print axioms binary_gain_split_fintype_capacity

end JSP000404Research
