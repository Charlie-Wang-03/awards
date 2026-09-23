
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Rank-one block capacity bridge

Sendov's 1995 Lemma 4.12 is a statement about a perfect generalized
configuration decomposed into rank-one circles.

At the top level there are centres i.  The points inside the i-th rank-one
circle form a block P_i.  Lemma 4.10 gives a local estimate

  card(P_i) <= 2^(k_i),

where k_i is computed from the projective gap cycle of the rank-one centres.
If the rank-one blocks partition the whole point set, then the global point
count is bounded by the sum of these dyadic centre weights.

Thus the genuinely difficult geometric/combinatorial statement is precisely

  sum_i 2^(k_i) <= 2^n.

This file isolates the elementary block-summing bridge so that the centre-level
research modules can be connected cleanly to the original 1995 formulation.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Finite partition form: disjoint rank-one blocks whose local sizes are
bounded by dyadic centre weights inherit the global dyadic capacity. -/
theorem rankOne_blocks_card_le_of_dyadic_capacity
    {I P : Type*} [Fintype I] [Fintype P]
    (block : I → Finset P)
    (exponent : I → ℕ)
    (hpairwise :
      ((Finset.univ : Finset I) : Set I).PairwiseDisjoint block)
    (hcover :
      (Finset.univ : Finset I).biUnion block =
        (Finset.univ : Finset P))
    (hlocal :
      ∀ i : I, (block i).card ≤ 2 ^ exponent i)
    {n : ℕ}
    (hcentre :
      (∑ i : I, 2 ^ exponent i) ≤ 2 ^ n) :
    Fintype.card P ≤ 2 ^ n := by
  classical
  have hcardUnion :
      ((Finset.univ : Finset I).biUnion block).card =
        ∑ i : I, (block i).card := by
    rw [Finset.card_biUnion hpairwise]
  have hsumLocal :
      (∑ i : I, (block i).card) ≤
        ∑ i : I, 2 ^ exponent i := by
    exact Finset.sum_le_sum fun i _ => hlocal i
  have hP :
      Fintype.card P =
        ((Finset.univ : Finset I).biUnion block).card := by
    rw [hcover]
    simp
  rw [hP, hcardUnion]
  exact hsumLocal.trans hcentre

/-- Exact perfect-block form, corresponding to Sendov's Lemma 4.7 when every
rank-one block has exactly 2^k points. -/
theorem rankOne_blocks_card_eq_dyadic_sum
    {I P : Type*} [Fintype I] [Fintype P]
    (block : I → Finset P)
    (exponent : I → ℕ)
    (hpairwise :
      ((Finset.univ : Finset I) : Set I).PairwiseDisjoint block)
    (hcover :
      (Finset.univ : Finset I).biUnion block =
        (Finset.univ : Finset P))
    (hexact :
      ∀ i : I, (block i).card = 2 ^ exponent i) :
    Fintype.card P = ∑ i : I, 2 ^ exponent i := by
  classical
  have hcardUnion :
      ((Finset.univ : Finset I).biUnion block).card =
        ∑ i : I, (block i).card := by
    rw [Finset.card_biUnion hpairwise]
  calc
    Fintype.card P
        = ((Finset.univ : Finset I).biUnion block).card := by
            rw [hcover]
            simp
    _ = ∑ i : I, (block i).card := hcardUnion
    _ = ∑ i : I, 2 ^ exponent i := by
          apply Finset.sum_congr rfl
          intro i _
          exact hexact i

#print axioms rankOne_blocks_card_le_of_dyadic_capacity
#print axioms rankOne_blocks_card_eq_dyadic_sum

end JSP000404Research
