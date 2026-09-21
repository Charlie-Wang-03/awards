import JSP000404Research.OrderedEdgeColor
import Mathlib.Tactic

/-!
# Permuted / aggregate weighted capacity

The Sendov target only involves the total dyadic mass

  sum_v 2 ^ exponent(v).

Therefore it is stronger than necessary to require vertex v itself to have at
least exponent(v) free Boolean coordinates in one even partition.

It is enough that the multiset of free-coordinate counts dominates the
multiset of exponents after a permutation of the vertices.  Equivalently, one
may match every exponent to a (possibly different) vertex with at least that
many free coordinates.

This is the natural aggregate outlet suggested by the original
Erdos--Szekeres weighted missing-colour lemma and by Sendov's use of extremal
exponent profiles.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

theorem permuted_exponent_capacity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V n)
    (exponent : V → ℕ)
    (sigma : Equiv.Perm V)
    (hpair :
      ∀ v,
        exponent v ≤
          n - (active C (sigma v)).card) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  have hpoint :
      ∀ v,
        2 ^ exponent v ≤
          2 ^ (n - (active C (sigma v)).card) := by
    intro v
    exact Nat.pow_le_pow_right
      (by norm_num : 0 < 2) (hpair v)
  have hsum :
      (∑ v, 2 ^ exponent v) ≤
        ∑ v, 2 ^ (n - (active C (sigma v)).card) :=
    Finset.sum_le_sum fun v _ => hpoint v
  have hperm :
      (∑ v, 2 ^ (n - (active C (sigma v)).card)) =
        ∑ w, 2 ^ (n - (active C w).card) := by
    simpa using
      (Equiv.sum_comp sigma
        (fun w : V => 2 ^ (n - (active C w).card)))
  rw [hperm] at hsum
  exact hsum.trans C.weighted_capacity

/-- Deficit formulation: the exponents need only be paired with the free
coordinate counts globally, not at the same vertices. -/
theorem permuted_deficit_capacity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V n)
    (exponent ell : V → ℕ)
    (sigma : Equiv.Perm V)
    (hexp : ∀ v, exponent v ≤ n)
    (hell : ∀ v, ell v = n - exponent v)
    (hpalette :
      ∀ v,
        (active C (sigma v)).card ≤ ell v) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  apply permuted_exponent_capacity C exponent sigma
  intro v
  rw [hell v]
  omega

/-- Exact multiset realization: if free-coordinate counts are exactly the
exponent profile after a permutation, capacity follows immediately. -/
theorem capacity_of_free_profile_permutation
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V n)
    (exponent : V → ℕ)
    (sigma : Equiv.Perm V)
    (hfree :
      ∀ v,
        n - (active C (sigma v)).card = exponent v) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  exact permuted_exponent_capacity C exponent sigma
    (fun v => by rw [hfree v])

#print axioms permuted_exponent_capacity
#print axioms permuted_deficit_capacity
#print axioms capacity_of_free_profile_permutation

end OrderedEdgeColoring
end JSP000404Research
