import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Abstract compensated deletion

The disputed Sendov extremizer is stronger than what an induction actually
needs.  Suppose a centre `r` is deleted.  Let `exponent` be the old
cluster exponents and `after` the exponents of the surviving centres after
the adjacent-gap merge.

If the surviving post-deletion weights are large enough to pay both the old
surviving weights and the deleted weight, then any inductive upper bound for
the post-deletion configuration immediately transfers to the original one.

A useful sufficient condition is weaker and local: if exponents never decrease,
and a set of surviving centres gains at least one exponent unit whose *old*
weights already sum to at least the deleted weight, then the payment condition
holds.  Each one-unit gain doubles that centre's weight.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Direct abstract compensated-deletion step. -/
theorem compensated_deletion
    {V : Type*} [Fintype V]
    (exponent after : V → ℕ) (r : V) (bound : ℕ)
    (hpay :
      2 ^ exponent r +
          ∑ i ∈ (Finset.univ.erase r), 2 ^ exponent i
        ≤ ∑ i ∈ (Finset.univ.erase r), 2 ^ after i)
    (hind :
      ∑ i ∈ (Finset.univ.erase r), 2 ^ after i ≤ bound) :
    ∑ i : V, 2 ^ exponent i ≤ bound := by
  classical
  have hsplit :
      ∑ i : V, 2 ^ exponent i =
        2 ^ exponent r +
          ∑ i ∈ (Finset.univ.erase r), 2 ^ exponent i := by
    rw [← Finset.add_sum_erase (Finset.univ : Finset V)
      (fun i => 2 ^ exponent i) (Finset.mem_univ r)]
    simp
  rw [hsplit]
  exact hpay.trans hind

/-- A one-unit exponent gain doubles the corresponding dyadic weight. -/
theorem two_mul_pow_le_pow_of_succ_le
    {a b : ℕ} (h : a + 1 ≤ b) :
    2 * 2 ^ a ≤ 2 ^ b := by
  have hp : 2 ^ (a + 1) ≤ 2 ^ b :=
    Nat.pow_le_pow_right (by norm_num) h
  simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hp

/-- Pointwise payment inequality: on a designated gain set, one extra old
weight is absorbed by a one-unit exponent increase; outside it, mere
monotonicity suffices. -/
theorem gain_set_sum_payment
    {V : Type*} [Fintype V]
    (exponent after : V → ℕ) (r : V)
    (gain : Finset V)
    (hgain_sub : gain ⊆ Finset.univ.erase r)
    (hmono : ∀ i ∈ Finset.univ.erase r, exponent i ≤ after i)
    (hgain : ∀ i ∈ gain, exponent i + 1 ≤ after i) :
    (∑ i ∈ Finset.univ.erase r, 2 ^ exponent i) +
        ∑ i ∈ gain, 2 ^ exponent i
      ≤ ∑ i ∈ Finset.univ.erase r, 2 ^ after i := by
  classical
  rw [← Finset.sum_add_sum_compl hgain_sub]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hig : i ∈ gain
  · simp only [Finset.mem_sdiff, hig, not_true_eq_false, and_false,
      Finset.sum_empty, add_zero] at *
    have hdouble :=
      two_mul_pow_le_pow_of_succ_le (hgain i hig)
    simpa [hig, two_mul] using hdouble
  · have hm := hmono i hi
    have hp : 2 ^ exponent i ≤ 2 ^ after i :=
      Nat.pow_le_pow_right (by norm_num) hm
    simp [hig, hp]

/-- Weighted-neighbourhood criterion for compensated deletion.

If the old weights of centres gaining at least one exponent unit already cover
the deleted centre's weight, then the post-deletion survivors pay for the
entire original configuration.
-/
theorem deletion_payment_of_gain_mass
    {V : Type*} [Fintype V]
    (exponent after : V → ℕ) (r : V)
    (gain : Finset V)
    (hgain_sub : gain ⊆ Finset.univ.erase r)
    (hmono : ∀ i ∈ Finset.univ.erase r, exponent i ≤ after i)
    (hgain : ∀ i ∈ gain, exponent i + 1 ≤ after i)
    (hmass : 2 ^ exponent r ≤ ∑ i ∈ gain, 2 ^ exponent i) :
    2 ^ exponent r +
          ∑ i ∈ Finset.univ.erase r, 2 ^ exponent i
      ≤ ∑ i ∈ Finset.univ.erase r, 2 ^ after i := by
  have hsum :=
    gain_set_sum_payment exponent after r gain hgain_sub hmono hgain
  omega

/-- Ready-to-use induction rule in terms of the weighted gain neighbourhood. -/
theorem compensated_deletion_of_gain_mass
    {V : Type*} [Fintype V]
    (exponent after : V → ℕ) (r : V)
    (gain : Finset V) (bound : ℕ)
    (hgain_sub : gain ⊆ Finset.univ.erase r)
    (hmono : ∀ i ∈ Finset.univ.erase r, exponent i ≤ after i)
    (hgain : ∀ i ∈ gain, exponent i + 1 ≤ after i)
    (hmass : 2 ^ exponent r ≤ ∑ i ∈ gain, 2 ^ exponent i)
    (hind : ∑ i ∈ Finset.univ.erase r, 2 ^ after i ≤ bound) :
    ∑ i : V, 2 ^ exponent i ≤ bound := by
  apply compensated_deletion exponent after r bound
  · exact deletion_payment_of_gain_mass
      exponent after r gain hgain_sub hmono hgain hmass
  · exact hind

#print axioms compensated_deletion
#print axioms two_mul_pow_le_pow_of_succ_le
#print axioms gain_set_sum_payment
#print axioms deletion_payment_of_gain_mass
#print axioms compensated_deletion_of_gain_mass

end JSP000404Research
