
import JSP000404Research.MinimalOverweightDyadicRigidity
import Mathlib.Tactic

/-!
# Normalized Kraft profile of a minimal overweight step

Let r be a minimum-exponent vertex and assume its deletion child is bounded.
MinimalOverweightDyadicRigidity gives

  sum_{i != r} 2^k_i = 2^n

and

  sum_i 2^k_i = 2^n + 2^a,

where a = k_r.

Because a <= k_i and a <= n, divide every term by the common factor 2^a.
The survivor profile satisfies the exact normalized Kraft equality

  sum_{i != r} 2^(k_i-a) = 2^(n-a),

while the full overweight profile satisfies

  sum_i 2^(k_i-a) = 2^(n-a) + 1.

Thus a minimal overweight profile is literally one extra minimum dyadic atom
sitting on top of a full binary Kraft equality profile.
-/

namespace JSP000404Research

open scoped BigOperators

def normalizedExponent
    {V : Type*}
    (exponent : V → ℕ)
    (r i : V) : ℕ :=
  exponent i - exponent r

def normalizedOldDeletionWeight
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (r : V) : ℕ :=
  ∑ i ∈ Finset.univ.erase r,
    2 ^ normalizedExponent exponent r i

def normalizedTotalDyadicWeight
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (r : V) : ℕ :=
  ∑ i : V, 2 ^ normalizedExponent exponent r i

theorem dyadic_term_factor_min
    {V : Type*}
    (exponent : V → ℕ)
    {r i : V}
    (hmin : exponent r ≤ exponent i) :
    2 ^ exponent i =
      2 ^ exponent r *
        2 ^ normalizedExponent exponent r i := by
  unfold normalizedExponent
  rw [← pow_add]
  congr 1
  omega

theorem bound_factor_min
    {a n : ℕ}
    (han : a ≤ n) :
    2 ^ n = 2 ^ a * 2 ^ (n - a) := by
  rw [← pow_add]
  congr 1
  omega

/-- Factor the minimum dyadic atom from the old survivor mass. -/
theorem oldDeletionWeight_eq_minFactor_mul_normalized
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (r : V)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    oldDeletionWeight exponent r =
      2 ^ exponent r *
        normalizedOldDeletionWeight exponent r := by
  classical
  unfold oldDeletionWeight normalizedOldDeletionWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact dyadic_term_factor_min exponent (hmin i)

/-- Exact normalized Kraft equality on the survivors of a bounded minimum
deletion. -/
theorem normalized_survivor_kraft_equality_of_child_bound
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (r : V)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hmonoR :
      ∀ i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchildR :
      deletionPostWeight after r ≤ 2 ^ n)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    normalizedOldDeletionWeight exponent r =
      2 ^ (n - exponent r) := by
  have hold :=
    oldDeletionWeight_eq_bound_of_minimum_child_bound
      exponent after n r hexp hmonoR hover hchildR hmin
  have hfactor :=
    oldDeletionWeight_eq_minFactor_mul_normalized
      exponent r hmin
  have hbound :=
    bound_factor_min (hexp r)
  rw [hfactor, hbound] at hold
  exact Nat.mul_left_cancel
    (by positivity : 0 < 2 ^ exponent r)
    hold

/-- The normalized minimum vertex itself contributes exactly one. -/
@[simp] theorem normalizedExponent_self
    {V : Type*}
    (exponent : V → ℕ)
    (r : V) :
    normalizedExponent exponent r r = 0 := by
  simp [normalizedExponent]

/-- Full normalized total equals survivor normalized mass plus the one minimum
atom. -/
theorem normalizedTotal_eq_one_add_survivor
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (r : V) :
    normalizedTotalDyadicWeight exponent r =
      1 + normalizedOldDeletionWeight exponent r := by
  classical
  unfold normalizedTotalDyadicWeight
  rw [← Finset.add_sum_erase
    (Finset.univ : Finset V)
    (fun i => 2 ^ normalizedExponent exponent r i)
    (Finset.mem_univ r)]
  simp [normalizedOldDeletionWeight,
    normalizedExponent, Nat.add_comm]

/-- Main profile form: the whole minimal overweight profile is one above an
exact normalized Kraft equality. -/
theorem normalized_total_eq_kraft_plus_one_of_child_bound
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (r : V)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hmonoR :
      ∀ i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchildR :
      deletionPostWeight after r ≤ 2 ^ n)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    normalizedTotalDyadicWeight exponent r =
      2 ^ (n - exponent r) + 1 := by
  rw [normalizedTotal_eq_one_add_survivor]
  rw [normalized_survivor_kraft_equality_of_child_bound
    exponent after n r hexp hmonoR hover hchildR hmin]
  omega

/-- Equivalent unnormalized exact total formula. -/
theorem total_weight_eq_bound_add_min_weight_of_child_bound
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (r : V)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hmonoR :
      ∀ i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchildR :
      deletionPostWeight after r ≤ 2 ^ n)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    (∑ i : V, 2 ^ exponent i) =
      2 ^ n + 2 ^ exponent r := by
  have hE :=
    minimal_overweight_excess_eq_min_weight_of_child_bound
      exponent after n r hexp hmonoR hover hchildR hmin
  have hle :
      2 ^ n ≤ ∑ i : V, 2 ^ exponent i :=
    le_of_lt hover
  omega

#print axioms oldDeletionWeight_eq_minFactor_mul_normalized
#print axioms normalized_survivor_kraft_equality_of_child_bound
#print axioms normalized_total_eq_kraft_plus_one_of_child_bound
#print axioms total_weight_eq_bound_add_min_weight_of_child_bound

end JSP000404Research
