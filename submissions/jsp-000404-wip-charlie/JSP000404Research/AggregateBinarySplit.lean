import Mathlib.Tactic

/-!
# Aggregate binary split induction

Pointwise +1 gain at every survivor is sufficient but unnecessarily strong.
The arithmetic induction only needs a child-level mass doubling condition.

Let S=A ⊔ B.  If, after deleting the opposite child,

  2 * oldMass(A) <= postMass(A),
  2 * oldMass(B) <= postMass(B),

and both child post configurations satisfy the ordinary capacity bound

  postMass(A), postMass(B) <= 2^n,

then

  oldMass(S) <= 2^n.

This strictly weakens BinaryGainSplit: no individual survivor is required to
gain one exponent unit.  Gains may be redistributed inside each child.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Main aggregate binary split step. -/
theorem aggregate_binary_split_capacity_step
    {V : Type*}
    (S A B : Finset V)
    (old postA postB : V → ℕ)
    (n : ℕ)
    (hdisj : Disjoint A B)
    (hunion : S = A ∪ B)
    (hdoubleA :
      2 * (∑ v ∈ A, 2 ^ old v) ≤
        ∑ v ∈ A, 2 ^ postA v)
    (hdoubleB :
      2 * (∑ v ∈ B, 2 ^ old v) ≤
        ∑ v ∈ B, 2 ^ postB v)
    (hcapA :
      (∑ v ∈ A, 2 ^ postA v) ≤ 2 ^ n)
    (hcapB :
      (∑ v ∈ B, 2 ^ postB v) ≤ 2 ^ n) :
    (∑ v ∈ S, 2 ^ old v) ≤ 2 ^ n := by
  have hA :
      2 * (∑ v ∈ A, 2 ^ old v) ≤ 2 ^ n :=
    hdoubleA.trans hcapA
  have hB :
      2 * (∑ v ∈ B, 2 ^ old v) ≤ 2 ^ n :=
    hdoubleB.trans hcapB
  have hparent :
      (∑ v ∈ S, 2 ^ old v) =
        (∑ v ∈ A, 2 ^ old v) +
        (∑ v ∈ B, 2 ^ old v) := by
    rw [hunion, Finset.sum_union hdisj]
  rw [hparent]
  omega

/-- Fintype specialization for a full partition. -/
theorem aggregate_binary_split_fintype_capacity
    {V : Type*} [Fintype V]
    (A B : Finset V)
    (old postA postB : V → ℕ)
    (n : ℕ)
    (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ)
    (hdoubleA :
      2 * (∑ v ∈ A, 2 ^ old v) ≤
        ∑ v ∈ A, 2 ^ postA v)
    (hdoubleB :
      2 * (∑ v ∈ B, 2 ^ old v) ≤
        ∑ v ∈ B, 2 ^ postB v)
    (hcapA :
      (∑ v ∈ A, 2 ^ postA v) ≤ 2 ^ n)
    (hcapB :
      (∑ v ∈ B, 2 ^ postB v) ≤ 2 ^ n) :
    (∑ v : V, 2 ^ old v) ≤ 2 ^ n := by
  exact aggregate_binary_split_capacity_step
    Finset.univ A B old postA postB n
    hdisj hcover.symm
    hdoubleA hdoubleB hcapA hcapB

/-- Pointwise gain implies the aggregate child-doubling hypothesis. -/
theorem aggregate_double_of_pointwise_gain
    {V : Type*}
    (A : Finset V)
    (old post : V → ℕ)
    (hgain : ∀ v ∈ A, old v + 1 ≤ post v) :
    2 * (∑ v ∈ A, 2 ^ old v) ≤
      ∑ v ∈ A, 2 ^ post v := by
  exact doubled_sum_le_post_sum_of_pointwise_gain
    A old post hgain

#print axioms aggregate_binary_split_capacity_step
#print axioms aggregate_binary_split_fintype_capacity
#print axioms aggregate_double_of_pointwise_gain

end JSP000404Research
