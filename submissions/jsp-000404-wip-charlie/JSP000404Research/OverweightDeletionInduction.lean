
import JSP000404Research.AggregateSplitTree
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Induction needs compensated deletion only in the overweight regime

Sendov's published Lemma 4.12 computes the cases with at most four top-level
centres and then invokes induction on the number of centres.

For a rigorous induction it is not necessary that every configuration admit a
compensated deletion.  Numerical exact-normalization examples show that this
stronger statement is false even for five centres.

The correct induction interface is strictly weaker:

* small configurations (here card <= 4) satisfy the target capacity directly;
* if a larger configuration is OVER the target capacity, then one may delete
  a centre without decreasing the total fixed-parameter dyadic mass.

The second condition alone contradicts minimality of an overweight
counterexample.  Configurations below the target are irrelevant even if every
deletion loses mass.

This file formalizes that minimal-counterexample induction independently of
the geometric existence theorem still required for JSP-000404.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Abstract overweight-only deletion induction on finite subsets. -/
theorem restricted_capacity_of_overweight_deletion
    {V : Type*} [DecidableEq V]
    (exponent : Finset V → V → ℕ)
    (bound : ℕ)
    (hbase :
      ∀ S : Finset V,
        S.card ≤ 4 →
        restrictedDyadicWeight exponent S S ≤ bound)
    (hdelete :
      ∀ S : Finset V,
        5 ≤ S.card →
        bound < restrictedDyadicWeight exponent S S →
        ∃ r ∈ S,
          restrictedDyadicWeight exponent S S ≤
            restrictedDyadicWeight exponent (S.erase r) (S.erase r)) :
    ∀ S : Finset V,
      restrictedDyadicWeight exponent S S ≤ bound := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
      by_cases hsmall : S.card ≤ 4
      · exact hbase S hsmall
      · have hlarge : 5 ≤ S.card := by omega
        by_contra hnot
        have hover :
            bound < restrictedDyadicWeight exponent S S := by
          omega
        obtain ⟨r, hrS, hcomp⟩ :=
          hdelete S hlarge hover
        have hproper : S.erase r ⊂ S := by
          constructor
          · exact Finset.erase_subset r S
          · intro heq
            have hrErase : r ∉ S.erase r := by simp
            exact hrErase (by
              rw [heq]
              exact hrS)
        have hchild :
            restrictedDyadicWeight exponent
                (S.erase r) (S.erase r) ≤ bound :=
          ih (S.erase r) hproper
        omega

/-- Full finite-type form. -/
theorem univ_capacity_of_overweight_deletion
    {V : Type*} [Fintype V] [DecidableEq V]
    (exponent : Finset V → V → ℕ)
    (bound : ℕ)
    (hbase :
      ∀ S : Finset V,
        S.card ≤ 4 →
        restrictedDyadicWeight exponent S S ≤ bound)
    (hdelete :
      ∀ S : Finset V,
        5 ≤ S.card →
        bound < restrictedDyadicWeight exponent S S →
        ∃ r ∈ S,
          restrictedDyadicWeight exponent S S ≤
            restrictedDyadicWeight exponent (S.erase r) (S.erase r)) :
    (∑ v : V, 2 ^ exponent Finset.univ v) ≤ bound := by
  have h :=
    restricted_capacity_of_overweight_deletion
      exponent bound hbase hdelete (Finset.univ : Finset V)
  simpa [restrictedDyadicWeight] using h

/-- Sendov lower-branch specialization of the abstract bound. -/
theorem univ_two_pow_capacity_of_overweight_deletion
    {V : Type*} [Fintype V] [DecidableEq V]
    (exponent : Finset V → V → ℕ)
    (n : ℕ)
    (hbase :
      ∀ S : Finset V,
        S.card ≤ 4 →
        restrictedDyadicWeight exponent S S ≤ 2 ^ n)
    (hdelete :
      ∀ S : Finset V,
        5 ≤ S.card →
        2 ^ n < restrictedDyadicWeight exponent S S →
        ∃ r ∈ S,
          restrictedDyadicWeight exponent S S ≤
            restrictedDyadicWeight exponent (S.erase r) (S.erase r)) :
    (∑ v : V, 2 ^ exponent Finset.univ v) ≤ 2 ^ n :=
  univ_capacity_of_overweight_deletion
    exponent (2 ^ n) hbase hdelete

#print axioms restricted_capacity_of_overweight_deletion
#print axioms univ_capacity_of_overweight_deletion
#print axioms univ_two_pow_capacity_of_overweight_deletion

end JSP000404Research
