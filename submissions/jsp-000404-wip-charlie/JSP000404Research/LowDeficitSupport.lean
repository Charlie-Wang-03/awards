import JSP000404Research.ZeroCarry
import Mathlib.Tactic

/-!
# Low Sendov deficit forces low quotient support

The zero-carry decomposition

  ell = (n - sum q) + positiveSupport q

immediately implies

  positiveSupport q <= ell.

For the dangerous top dyadic layers this is especially rigid:

* ell <= 2  ->  support <= 2;
* k = floorExcess q >= n-2  ->  ell = n-k <= 2  ->  support <= 2.

Combined with the antiperiodic sign-transition lemmas, every centre of weight
at least 2^(n-2) belongs to the one-transition geometric regime.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Deficit at most two forces at most two positive quotient gaps. -/
theorem positiveSupport_le_two_of_deficit_le_two
    {I : Type*} [Fintype I]
    (q : I → ℕ) (n : ℕ)
    (hQ : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q ≤ 2) :
    positiveSupport q ≤ 2 :=
  positiveSupport_le_of_deficit_le q n 2 hQ hell

/-- More generally, an explicit deficit value bounds support by that value. -/
theorem positiveSupport_le_of_deficit_eq
    {I : Type*} [Fintype I]
    (q : I → ℕ) (n ell : ℕ)
    (hQ : (∑ i, q i) ≤ n)
    (hell : ell = n - floorExcess q) :
    positiveSupport q ≤ ell := by
  rw [hell]
  exact positiveSupport_le_deficit q n hQ

/-- An exponent in the top three dyadic layers has support at most two. -/
theorem positiveSupport_le_two_of_exponent_ge_n_sub_two
    {I : Type*} [Fintype I]
    (q : I → ℕ) (n : ℕ)
    (hQ : (∑ i, q i) ≤ n)
    (hexp : n - 2 ≤ floorExcess q)
    (hexp_le : floorExcess q ≤ n) :
    positiveSupport q ≤ 2 := by
  have hell : n - floorExcess q ≤ 2 := by
    omega
  exact positiveSupport_le_two_of_deficit_le_two q n hQ hell

/-- Equivalently, if ell = n-k and k >= n-2, quotient support is at most two. -/
theorem positiveSupport_le_two_of_large_exponent
    {I : Type*} [Fintype I]
    (q : I → ℕ) (n k ell : ℕ)
    (hQ : (∑ i, q i) ≤ n)
    (hk : k = floorExcess q)
    (hell : ell = n - k)
    (hlarge : n - 2 ≤ k) :
    positiveSupport q ≤ 2 := by
  subst k
  have hE : floorExcess q ≤ n := by
    exact (floorExcess_le_sum q).trans hQ
  have hdef : n - floorExcess q ≤ 2 := by omega
  exact positiveSupport_le_two_of_deficit_le_two q n hQ hdef

#print axioms positiveSupport_le_two_of_deficit_le_two
#print axioms positiveSupport_le_of_deficit_eq
#print axioms positiveSupport_le_two_of_exponent_ge_n_sub_two
#print axioms positiveSupport_le_two_of_large_exponent

end JSP000404Research
