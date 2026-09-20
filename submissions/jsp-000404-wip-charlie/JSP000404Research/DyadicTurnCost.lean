import JSP000404Research.SingleSupportDeficit
import Mathlib.Tactic

/-!
# Dyadic weight paid by normalized turn cost

For a one-support Sendov centre, the unique positive quotient q satisfies

  q = floorExcess + 1.

Thus, if the corresponding transition / exterior-turn gap is used as a
geometric payment, its normalized integer cost is exactly k+1 for exponent k.

This file also proves the pure dyadic knapsack estimate needed downstream:

if 1 <= n, every exponent k_i is < n, and

  sum_i (k_i + 1) <= 2*n,

then

  sum_i 2^(k_i) <= 2^n.

The pointwise inequality is

  n * 2^k <= (k+1) * 2^(n-1)     (k<n).

Hence a global two-turn-budget pays the entire dyadic mass of any family whose
geometric turn costs dominate k+1.
-/

namespace JSP000404Research

open scoped BigOperators

/-- With one positive quotient coordinate, its value is exactly exponent+1. -/
theorem unique_positive_quotient_eq_exponent_add_one
    {I : Type*} [Fintype I]
    (q : I → ℕ) (e : I)
    (hsupport : positiveSupport q = 1)
    (he : q e ≠ 0) :
    q e = floorExcess q + 1 := by
  classical
  obtain ⟨e0, he0, huniq⟩ :=
    existsUnique_positive_of_support_one q hsupport
  have heq : e = e0 := huniq e he
  subst e0
  have hsum : (∑ i, q i) = q e := by
    rw [Finset.sum_eq_single e]
    · intro b _ hbe
      by_contra hb
      exact hbe (huniq b hb)
    · intro heNot
      exact False.elim (heNot (Finset.mem_univ e))
  have hid := floorExcess_add_positiveSupport q
  rw [hsupport, hsum] at hid
  omega

/-- Elementary exponential estimate d+1 <= 2^d. -/
theorem succ_le_two_pow (d : ℕ) :
    d + 1 ≤ 2 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ]
      have hmul :
          2 * (d + 1) ≤ 2 * 2 ^ d :=
        Nat.mul_le_mul_left 2 ih
      omega

/-- Pointwise turn-cost payment for a dyadic exponent. -/
theorem n_mul_two_pow_le_cost_mul_top_pow
    {n k : ℕ}
    (hn : 1 ≤ n)
    (hk : k < n) :
    n * 2 ^ k ≤ (k + 1) * 2 ^ (n - 1) := by
  let d := n - 1 - k
  have hkTop : k ≤ n - 1 := by omega
  have hkd : k + d = n - 1 := by
    dsimp [d]
    omega
  have hbase :
      n ≤ (k + 1) * (d + 1) := by
    calc
      n = k + d + 1 := by omega
      _ ≤ k * d + (k + d + 1) := Nat.le_add_left _ _
      _ = (k + 1) * (d + 1) := by ring
  have hpow : d + 1 ≤ 2 ^ d := succ_le_two_pow d
  have hcost :
      n ≤ (k + 1) * 2 ^ d :=
    hbase.trans (Nat.mul_le_mul_left (k + 1) hpow)
  calc
    n * 2 ^ k
        ≤ ((k + 1) * 2 ^ d) * 2 ^ k :=
          Nat.mul_le_mul_right (2 ^ k) hcost
    _ = (k + 1) * 2 ^ (n - 1) := by
      rw [← pow_add]
      have : d + k = n - 1 := by omega
      rw [this]
      ring

/-- Main dyadic turn-cost knapsack theorem. -/
theorem dyadic_sum_le_two_pow_of_turn_cost
    {I : Type*} [Fintype I]
    (exponent : I → ℕ)
    (n : ℕ)
    (hn : 1 ≤ n)
    (hexp : ∀ i, exponent i < n)
    (hcost :
      (∑ i, (exponent i + 1)) ≤ 2 * n) :
    (∑ i, 2 ^ exponent i) ≤ 2 ^ n := by
  have hpoint :
      ∀ i : I,
        n * 2 ^ exponent i ≤
          (exponent i + 1) * 2 ^ (n - 1) := by
    intro i
    exact n_mul_two_pow_le_cost_mul_top_pow
      hn (hexp i)
  have hsum :
      (∑ i : I, n * 2 ^ exponent i) ≤
        ∑ i : I, (exponent i + 1) * 2 ^ (n - 1) :=
    Finset.sum_le_sum fun i _ => hpoint i
  have hscaled :
      n * (∑ i : I, 2 ^ exponent i) ≤
        (∑ i : I, (exponent i + 1)) * 2 ^ (n - 1) := by
    simpa [Finset.mul_sum, Finset.sum_mul] using hsum
  have hbudget :
      (∑ i : I, (exponent i + 1)) * 2 ^ (n - 1) ≤
        (2 * n) * 2 ^ (n - 1) :=
    Nat.mul_le_mul_right (2 ^ (n - 1)) hcost
  have htop :
      (2 * n) * 2 ^ (n - 1) = n * 2 ^ n := by
    have hnsub : n - 1 + 1 = n := by omega
    calc
      (2 * n) * 2 ^ (n - 1)
          = n * (2 ^ (n - 1) * 2) := by ring
      _ = n * 2 ^ n := by
        rw [← pow_succ, hnsub]
  have hmul :
      n * (∑ i : I, 2 ^ exponent i) ≤
        n * 2 ^ n :=
    hscaled.trans (hbudget.trans_eq htop)
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

/-- A slightly more flexible form: any integer cost dominating k+1 works. -/
theorem dyadic_sum_le_two_pow_of_dominating_cost
    {I : Type*} [Fintype I]
    (exponent cost : I → ℕ)
    (n : ℕ)
    (hn : 1 ≤ n)
    (hexp : ∀ i, exponent i < n)
    (hdom : ∀ i, exponent i + 1 ≤ cost i)
    (hcost : (∑ i, cost i) ≤ 2 * n) :
    (∑ i, 2 ^ exponent i) ≤ 2 ^ n := by
  apply dyadic_sum_le_two_pow_of_turn_cost exponent n hn hexp
  exact (Finset.sum_le_sum fun i _ => hdom i).trans hcost

#print axioms unique_positive_quotient_eq_exponent_add_one
#print axioms succ_le_two_pow
#print axioms n_mul_two_pow_le_cost_mul_top_pow
#print axioms dyadic_sum_le_two_pow_of_turn_cost
#print axioms dyadic_sum_le_two_pow_of_dominating_cost

end JSP000404Research
