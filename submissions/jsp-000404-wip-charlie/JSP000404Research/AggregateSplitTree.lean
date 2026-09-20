import Mathlib.Tactic

/-!
# Aggregate binary split trees at one fixed Sendov parameter

Pointwise +1 gain at every survivor is stronger than necessary and has a
five-point hard stop.  The correct recursive inequality may only need total
dyadic mass to double on each child.

Fix an abstract exponent profile

  exponent S v

for vertex v when the current retained top-level set is S.

At a split S = A disjoint-union B require only

  2 * sum_{v in A} 2^(exponent S v)
      <= sum_{v in A} 2^(exponent A v)

and similarly for B.

A leaf may close by any direct capacity proof for its restricted profile
(e.g. the two-centre terminal case).

This file proves that any such recursive certificate bounds the root mass by
2^n.  No exact-normalization theorem is applied to child subsets: all
restricted profiles are part of the one fixed-parameter certificate.
-/

namespace JSP000404Research

open scoped BigOperators

def restrictedDyadicWeight
    {V : Type*}
    (exponent : Finset V → V → ℕ)
    (ambient subset : Finset V) : ℕ :=
  ∑ v ∈ subset, 2 ^ exponent ambient v

inductive AggregateSplitTree
    {V : Type*}
    (exponent : Finset V → V → ℕ)
    (n : ℕ) :
    Finset V → Type
  | leaf (S : Finset V)
      (hcap :
        restrictedDyadicWeight exponent S S ≤ 2 ^ n) :
      AggregateSplitTree exponent n S
  | node
      {S A B : Finset V}
      (hdisj : Disjoint A B)
      (hunion : S = A ∪ B)
      (hdoubleA :
        2 * restrictedDyadicWeight exponent S A ≤
          restrictedDyadicWeight exponent A A)
      (hdoubleB :
        2 * restrictedDyadicWeight exponent S B ≤
          restrictedDyadicWeight exponent B B)
      (left : AggregateSplitTree exponent n A)
      (right : AggregateSplitTree exponent n B) :
      AggregateSplitTree exponent n S

namespace AggregateSplitTree

/-- Every aggregate split tree certifies the sharp root dyadic capacity. -/
theorem capacity
    {V : Type*}
    {exponent : Finset V → V → ℕ}
    {n : ℕ} {S : Finset V}
    (T : AggregateSplitTree exponent n S) :
    restrictedDyadicWeight exponent S S ≤ 2 ^ n := by
  induction T with
  | leaf S hcap =>
      exact hcap
  | @node S A B hdisj hunion hdoubleA hdoubleB left right ihA ihB =>
      have hA :
          2 * restrictedDyadicWeight exponent S A ≤ 2 ^ n :=
        hdoubleA.trans ihA
      have hB :
          2 * restrictedDyadicWeight exponent S B ≤ 2 ^ n :=
        hdoubleB.trans ihB
      have hsum :
          2 * (restrictedDyadicWeight exponent S A +
            restrictedDyadicWeight exponent S B) ≤
              2 * 2 ^ n := by
        omega
      have hroot :
          restrictedDyadicWeight exponent S S =
            restrictedDyadicWeight exponent S A +
              restrictedDyadicWeight exponent S B := by
        unfold restrictedDyadicWeight
        rw [hunion, Finset.sum_union hdisj]
      rw [hroot]
      omega

/-- Convenience form: a certified full finite vertex set has capacity 2^n. -/
theorem univ_capacity
    {V : Type*} [Fintype V]
    {exponent : Finset V → V → ℕ}
    {n : ℕ}
    (T : AggregateSplitTree exponent n Finset.univ) :
    (∑ v : V, 2 ^ exponent Finset.univ v) ≤ 2 ^ n := by
  simpa [restrictedDyadicWeight] using T.capacity

/-- A two-child one-step constructor with already certified children. -/
theorem capacity_of_split
    {V : Type*}
    {exponent : Finset V → V → ℕ}
    {n : ℕ}
    {S A B : Finset V}
    (hdisj : Disjoint A B)
    (hunion : S = A ∪ B)
    (hdoubleA :
      2 * restrictedDyadicWeight exponent S A ≤
        restrictedDyadicWeight exponent A A)
    (hdoubleB :
      2 * restrictedDyadicWeight exponent S B ≤
        restrictedDyadicWeight exponent B B)
    (hcapA :
      restrictedDyadicWeight exponent A A ≤ 2 ^ n)
    (hcapB :
      restrictedDyadicWeight exponent B B ≤ 2 ^ n) :
    restrictedDyadicWeight exponent S S ≤ 2 ^ n := by
  exact (AggregateSplitTree.node
    hdisj hunion hdoubleA hdoubleB
    (AggregateSplitTree.leaf A hcapA)
    (AggregateSplitTree.leaf B hcapB)).capacity

#print axioms AggregateSplitTree.capacity
#print axioms AggregateSplitTree.univ_capacity
#print axioms AggregateSplitTree.capacity_of_split

end AggregateSplitTree
end JSP000404Research
