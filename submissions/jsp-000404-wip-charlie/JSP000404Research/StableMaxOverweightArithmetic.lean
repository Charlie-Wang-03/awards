
import Mathlib.Tactic

/-!
# Arithmetic obstruction for an overweight configuration with a stable maximum

Let kStar be a maximal exponent and let h be any local support parameter for
that maximal centre satisfying

  kStar + h <= n.

If every exponent is at most kStar, then

  sum_v 2^(exponent v) <= card(V) * 2^kStar.

Consequently an overweight profile

  2^n < sum_v 2^(exponent v)

forces

  2^h < card(V).

Equivalently, if card(V) <= 2^h then the global dyadic target already follows.

This is the purely arithmetic endpoint of the concrete stable-centre support
reduction.  No geometric hypothesis is used here.
-/

namespace JSP000404Research

open scoped BigOperators

/-- A global maximal exponent bounds total dyadic mass by cardinality times the
maximal dyadic weight. -/
theorem dyadic_sum_le_card_mul_pow_of_max
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (kStar : ℕ)
    (hmax : ∀ v, exponent v ≤ kStar) :
    (∑ v : V, 2 ^ exponent v) ≤
      Fintype.card V * 2 ^ kStar := by
  calc
    (∑ v : V, 2 ^ exponent v)
        ≤ ∑ _v : V, 2 ^ kStar := by
          apply Finset.sum_le_sum
          intro v _
          exact Nat.pow_le_pow_right
            (by norm_num : 0 < 2)
            (hmax v)
    _ = Fintype.card V * 2 ^ kStar := by
          simp [Finset.sum_const, Nat.mul_comm]

/-- If the number of vertices fits inside the local support Kraft capacity,
the global dyadic target follows. -/
theorem dyadic_capacity_of_card_le_pow_support
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (n kStar h : ℕ)
    (hmax : ∀ v, exponent v ≤ kStar)
    (hbudget : kStar + h ≤ n)
    (hcard : Fintype.card V ≤ 2 ^ h) :
    (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n := by
  have hmass :=
    dyadic_sum_le_card_mul_pow_of_max
      exponent kStar hmax
  have hmul :
      Fintype.card V * 2 ^ kStar
        ≤ 2 ^ h * 2 ^ kStar := by
    exact Nat.mul_le_mul_right (2 ^ kStar) hcard
  have hpowEq :
      2 ^ h * 2 ^ kStar = 2 ^ (h + kStar) := by
    rw [← pow_add]
  have hpow :
      2 ^ (h + kStar) ≤ 2 ^ n :=
    Nat.pow_le_pow_right
      (by norm_num : 0 < 2)
      (by omega)
  exact hmass.trans (hmul.trans (by
    rw [hpowEq]
    exact hpow))

/-- Contrapositive overweight form. -/
theorem pow_support_lt_card_of_overweight_max_budget
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (n kStar h : ℕ)
    (hmax : ∀ v, exponent v ≤ kStar)
    (hbudget : kStar + h ≤ n)
    (hover :
      2 ^ n < ∑ v : V, 2 ^ exponent v) :
    2 ^ h < Fintype.card V := by
  by_contra hnot
  have hcard :
      Fintype.card V ≤ 2 ^ h := by
    omega
  have hcap :=
    dyadic_capacity_of_card_le_pow_support
      exponent n kStar h hmax hbudget hcard
  omega

/-- Local-centre phrasing: a distinguished maximal centre with exponent kStar
and support h cannot occur in an overweight profile unless the ambient
configuration has more than 2^h vertices. -/
theorem pow_support_lt_card_of_overweight_distinguished_max
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (n h : ℕ)
    (i : V)
    (hmax : ∀ v, exponent v ≤ exponent i)
    (hbudget : exponent i + h ≤ n)
    (hover :
      2 ^ n < ∑ v : V, 2 ^ exponent v) :
    2 ^ h < Fintype.card V :=
  pow_support_lt_card_of_overweight_max_budget
    exponent n (exponent i) h hmax hbudget hover

#print axioms dyadic_sum_le_card_mul_pow_of_max
#print axioms dyadic_capacity_of_card_le_pow_support
#print axioms pow_support_lt_card_of_overweight_max_budget
#print axioms pow_support_lt_card_of_overweight_distinguished_max

end JSP000404Research
