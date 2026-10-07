import JSP000404Research.MinimalOverweightDyadicRigidity
import Mathlib.Tactic

/-!
# Lightweight zero-minimum overweight arithmetic

The exact +1 overweight conclusion for a zero minimum is purely dyadic
arithmetic.  It does not depend on the concrete planar deletion geometry or on
the unsafe zero-zero residual analysis.

Keeping this theorem in a lightweight module prevents global residual
accounting from importing the much heavier geometric deletion stack.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Exponent zero is automatically globally minimal. -/
theorem zero_exponent_is_minimum_arith
    {V : Type*}
    (exponent : V → ℕ)
    {r : V}
    (hr : exponent r = 0) :
    ∀ i : V, exponent r ≤ exponent i := by
  intro i
  rw [hr]
  exact Nat.zero_le _

/-- If a zero-minimum deletion child is bounded, the overweight total is
exactly one above the dyadic bound. -/
theorem zero_minimum_overweight_excess_eq_one_of_child_bound_arith
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
    (hrZero : exponent r = 0) :
    (∑ i : V, 2 ^ exponent i) = 2 ^ n + 1 := by
  have hmin : ∀ i : V, exponent r ≤ exponent i :=
    zero_exponent_is_minimum_arith exponent hrZero
  have hexcess :=
    minimal_overweight_excess_eq_min_weight_of_child_bound
      exponent after n r hexp hmonoR hover hchildR hmin
  rw [hrZero] at hexcess
  norm_num at hexcess
  have hle : 2 ^ n ≤ ∑ i : V, 2 ^ exponent i :=
    le_of_lt hover
  omega

#print axioms zero_exponent_is_minimum_arith
#print axioms zero_minimum_overweight_excess_eq_one_of_child_bound_arith

end JSP000404Research
