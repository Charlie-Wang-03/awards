import JSP000404Research.CompensatedDeletion
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Dyadic collisions and Huffman-style deletion

If all exponents lie below n and are pairwise distinct, their dyadic weights
occupy a subset of

  1, 2, 4, ..., 2^(n-1),

so the total is at most 2^n - 1.

Hence any hypothetical configuration with dyadic weight at least 2^n must
contain two distinct centres with equal exponent.  If one such equal-exponent
pair is geometrically mergeable -- deleting one centre raises the other's
exponent by at least one while all survivors are monotone -- then the gained
copy of 2^k exactly pays the deleted 2^k.  This is the Huffman-carry form of
the compensated-deletion strategy.
-/

namespace JSP000404Research

open scoped BigOperators

/-- The finite geometric sum of powers of two. -/
theorem sum_range_two_pow (n : ℕ) :
    (∑ k ∈ Finset.range n, 2 ^ k) = 2 ^ n - 1 := by
  have h :=
    geom_sum_mul_of_one_le (x := (2 : ℕ)) (by omega) n
  simpa using h

/-- Pairwise-distinct exponents below n have total dyadic mass at most
2^n-1. -/
theorem sum_pow_two_le_pred_of_injective
    {V : Type*} [Fintype V]
    (exponent : V → ℕ) (n : ℕ)
    (hinj : Function.Injective exponent)
    (hbound : ∀ v, exponent v < n) :
    (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n - 1 := by
  classical
  let S : Finset ℕ := Finset.univ.image exponent
  have hsum :
      (∑ v : V, 2 ^ exponent v) =
        ∑ k ∈ S, 2 ^ k := by
    dsimp [S]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hinj hab
  have hsub : S ⊆ Finset.range n := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨v, _, rfl⟩
    exact Finset.mem_range.mpr (hbound v)
  have hle :
      (∑ k ∈ S, 2 ^ k) ≤
        ∑ k ∈ Finset.range n, 2 ^ k := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      hsub (fun _ _ _ => Nat.zero_le _)
  rw [hsum, sum_range_two_pow] at hle
  exact hle

/-- Therefore mass at least 2^n forces an exponent collision. -/
theorem exists_equal_exponent_of_two_pow_le_sum
    {V : Type*} [Fintype V]
    (exponent : V → ℕ) (n : ℕ)
    (hbound : ∀ v, exponent v < n)
    (hmass : 2 ^ n ≤ ∑ v : V, 2 ^ exponent v) :
    ∃ r i : V, r ≠ i ∧ exponent r = exponent i := by
  by_contra hnone
  push_neg at hnone
  have hinj : Function.Injective exponent := by
    intro r i heq
    by_contra hri
    exact hnone r i hri heq
  have hle :=
    sum_pow_two_le_pred_of_injective exponent n hinj hbound
  have hpos : 0 < 2 ^ n := by positivity
  omega

/-- Equal exponents plus one survivor gain give exact dyadic payment. -/
theorem deletion_payment_of_equal_gain
    {V : Type*} [Fintype V]
    (exponent after : V → ℕ) {r i : V}
    (hri : r ≠ i)
    (heq : exponent r = exponent i)
    (hmono : ∀ j ∈ Finset.univ.erase r, exponent j ≤ after j)
    (hgain : exponent i + 1 ≤ after i) :
    2 ^ exponent r +
          ∑ j ∈ Finset.univ.erase r, 2 ^ exponent j
      ≤ ∑ j ∈ Finset.univ.erase r, 2 ^ after j := by
  exact deletion_payment_of_single_gain
    exponent after hri hmono hgain (by omega)

/-- Huffman carry induction outlet. -/
theorem compensated_deletion_of_equal_gain
    {V : Type*} [Fintype V]
    (exponent after : V → ℕ) {r i : V} (bound : ℕ)
    (hri : r ≠ i)
    (heq : exponent r = exponent i)
    (hmono : ∀ j ∈ Finset.univ.erase r, exponent j ≤ after j)
    (hgain : exponent i + 1 ≤ after i)
    (hind : ∑ j ∈ Finset.univ.erase r, 2 ^ after j ≤ bound) :
    ∑ j : V, 2 ^ exponent j ≤ bound := by
  apply compensated_deletion exponent after r bound
  · exact deletion_payment_of_equal_gain
      exponent after hri heq hmono hgain
  · exact hind

#print axioms sum_range_two_pow
#print axioms sum_pow_two_le_pred_of_injective
#print axioms exists_equal_exponent_of_two_pow_le_sum
#print axioms deletion_payment_of_equal_gain
#print axioms compensated_deletion_of_equal_gain

end JSP000404Research
