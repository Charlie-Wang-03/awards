import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Abstract compensated deletion

The disputed Sendov extremizer is stronger than what an induction actually
needs. Suppose a centre `r` is deleted. Let `exponent` be the old cluster
exponents and `after` the exponents of the surviving centres after the
adjacent-gap merge.

If the surviving post-deletion weights are large enough to pay both the old
surviving weights and the deleted weight, then any inductive upper bound for
the post-deletion configuration transfers to the original one.

A convenient sufficient condition is pointwise: attach a nonnegative
`bonus i` to each surviving centre. If
`2^exponent(i) + bonus(i) <= 2^after(i)`
for every survivor and the total bonus pays `2^exponent(r)`, the deletion is
valid. A one-unit exponent gain can supply the bonus `2^exponent(i)`.
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

/-- Pointwise bonus payment: if every survivor's post-deletion weight absorbs
its old weight plus a chosen bonus, and the bonuses pay the deleted weight,
then the whole deletion is compensated. -/
theorem deletion_payment_of_bonus
    {V : Type*} [Fintype V]
    (exponent after bonus : V → ℕ) (r : V)
    (hpoint : ∀ i ∈ Finset.univ.erase r,
      2 ^ exponent i + bonus i ≤ 2 ^ after i)
    (hmass :
      2 ^ exponent r ≤ ∑ i ∈ Finset.univ.erase r, bonus i) :
    2 ^ exponent r +
          ∑ i ∈ Finset.univ.erase r, 2 ^ exponent i
      ≤ ∑ i ∈ Finset.univ.erase r, 2 ^ after i := by
  classical
  have hsum :
      ∑ i ∈ Finset.univ.erase r, (2 ^ exponent i + bonus i)
        ≤ ∑ i ∈ Finset.univ.erase r, 2 ^ after i :=
    Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib] at hsum
  omega

/-- Ready-to-use induction rule with an arbitrary pointwise bonus. -/
theorem compensated_deletion_of_bonus
    {V : Type*} [Fintype V]
    (exponent after bonus : V → ℕ) (r : V) (bound : ℕ)
    (hpoint : ∀ i ∈ Finset.univ.erase r,
      2 ^ exponent i + bonus i ≤ 2 ^ after i)
    (hmass :
      2 ^ exponent r ≤ ∑ i ∈ Finset.univ.erase r, bonus i)
    (hind : ∑ i ∈ Finset.univ.erase r, 2 ^ after i ≤ bound) :
    ∑ i : V, 2 ^ exponent i ≤ bound := by
  apply compensated_deletion exponent after r bound
  · exact deletion_payment_of_bonus exponent after bonus r hpoint hmass
  · exact hind

/-- A single survivor gaining one exponent unit can pay a deleted centre whose
old exponent is no larger. -/
theorem deletion_payment_of_single_gain
    {V : Type*} [Fintype V]
    (exponent after : V → ℕ) {r i : V}
    (hri : r ≠ i)
    (hmono : ∀ j ∈ Finset.univ.erase r, exponent j ≤ after j)
    (hgain : exponent i + 1 ≤ after i)
    (hweight : exponent r ≤ exponent i) :
    2 ^ exponent r +
          ∑ j ∈ Finset.univ.erase r, 2 ^ exponent j
      ≤ ∑ j ∈ Finset.univ.erase r, 2 ^ after j := by
  classical
  let bonus : V → ℕ := fun j => if j = i then 2 ^ exponent i else 0
  apply deletion_payment_of_bonus exponent after bonus r
  · intro j hj
    by_cases hji : j = i
    · subst j
      have hdouble := two_mul_pow_le_pow_of_succ_le hgain
      simpa [bonus, two_mul] using hdouble
    · have hp : 2 ^ exponent j ≤ 2 ^ after j :=
        Nat.pow_le_pow_right (by norm_num) (hmono j hj)
      simp [bonus, hji, hp]
  · have hi : i ∈ Finset.univ.erase r := by
      simp [hri]
    have hpow : 2 ^ exponent r ≤ 2 ^ exponent i :=
      Nat.pow_le_pow_right (by norm_num) hweight
    have hterm :
        2 ^ exponent i ≤ ∑ j ∈ Finset.univ.erase r, bonus j := by
      calc
        2 ^ exponent i = bonus i := by simp [bonus]
        _ ≤ ∑ j ∈ Finset.univ.erase r, bonus j := by
          exact Finset.single_le_sum
            (fun _ _ => Nat.zero_le _)
            hi
    exact hpow.trans hterm

/-- Single-gain version of the induction step. -/
theorem compensated_deletion_of_single_gain
    {V : Type*} [Fintype V]
    (exponent after : V → ℕ) {r i : V} (bound : ℕ)
    (hri : r ≠ i)
    (hmono : ∀ j ∈ Finset.univ.erase r, exponent j ≤ after j)
    (hgain : exponent i + 1 ≤ after i)
    (hweight : exponent r ≤ exponent i)
    (hind : ∑ j ∈ Finset.univ.erase r, 2 ^ after j ≤ bound) :
    ∑ j : V, 2 ^ exponent j ≤ bound := by
  apply compensated_deletion exponent after r bound
  · exact deletion_payment_of_single_gain
      exponent after hri hmono hgain hweight
  · exact hind

#print axioms compensated_deletion
#print axioms two_mul_pow_le_pow_of_succ_le
#print axioms deletion_payment_of_bonus
#print axioms compensated_deletion_of_bonus
#print axioms deletion_payment_of_single_gain
#print axioms compensated_deletion_of_single_gain

end JSP000404Research
