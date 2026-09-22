
import JSP000404Research.ResidualOverlapCube
import JSP000404Research.ResidualSliceSeparation
import Mathlib.Tactic

/-!
# Strict projected slack pays pairwise overlap mass

For a residual-active vertex let

  nu(v) = projectedFree(C,v)
        = n - card(retainedActive(C,v)).

If an overlap carrier u,v has common-inactive dimension d, then

  d <= nu(u), d <= nu(v).

A purely dyadic lemma says that whenever

  x<a, y<b, d<=a, d<=b,

the two strict profile surpluses pay one d-dimensional overlap cube:

  2^d <= (2^a-2^x) + (2^b-2^y).

Therefore any projected overlap carrier whose two endpoints are both strictly
below their projected free dimensions is locally paid by endpoint profile
surplus.  Every genuinely unpaid carrier must have at least one saturated
endpoint.
-/

namespace JSP000404Research

/-- One strict dyadic slack contains at least the lower half of the ambient
dyadic block. -/
theorem half_pow_le_dyadic_surplus_of_lt
    {x a : ℕ}
    (hxa : x < a) :
    2 ^ (a - 1) ≤ 2 ^ a - 2 ^ x := by
  have haPos : 1 ≤ a := by omega
  have hxTop : x ≤ a - 1 := by omega
  have hxPow :
      2 ^ x ≤ 2 ^ (a - 1) :=
    Nat.pow_le_pow_right
      (by norm_num : 0 < 2) hxTop
  have hpow :
      2 ^ a = 2 ^ (a - 1) + 2 ^ (a - 1) := by
    have hsucc : a - 1 + 1 = a := by omega
    calc
      2 ^ a = 2 ^ (a - 1 + 1) := by rw [hsucc]
      _ = 2 ^ (a - 1) * 2 := by rw [pow_succ]
      _ = 2 ^ (a - 1) + 2 ^ (a - 1) := by omega
  omega

/-- Two strict dyadic profile slacks pay any common block whose dimension is
bounded by both free dimensions. -/
theorem pow_le_sum_dyadic_surplus_of_both_lt
    {d x y a b : ℕ}
    (hda : d ≤ a)
    (hdb : d ≤ b)
    (hxa : x < a)
    (hyb : y < b) :
    2 ^ d ≤
      (2 ^ a - 2 ^ x) +
      (2 ^ b - 2 ^ y) := by
  have hsurA :=
    half_pow_le_dyadic_surplus_of_lt hxa
  have hsurB :=
    half_pow_le_dyadic_surplus_of_lt hyb
  by_cases hdaStrict : d < a
  · have hdTop : d ≤ a - 1 := by omega
    have hp :
        2 ^ d ≤ 2 ^ (a - 1) :=
      Nat.pow_le_pow_right
        (by norm_num : 0 < 2) hdTop
    omega
  · have hdaEq : d = a := by omega
    by_cases hdbStrict : d < b
    · have hdTop : d ≤ b - 1 := by omega
      have hp :
          2 ^ d ≤ 2 ^ (b - 1) :=
        Nat.pow_le_pow_right
          (by norm_num : 0 < 2) hdTop
      omega
    · have hdbEq : d = b := by omega
      have hdPos : 1 ≤ d := by
        rw [hdaEq] at hxa
        omega
      have hdouble :
          2 ^ (d - 1) + 2 ^ (d - 1) = 2 ^ d := by
        have hsucc : d - 1 + 1 = d := by omega
        calc
          2 ^ (d - 1) + 2 ^ (d - 1)
              = 2 ^ (d - 1) * 2 := by omega
          _ = 2 ^ (d - 1 + 1) := by rw [pow_succ]
          _ = 2 ^ d := by rw [hsucc]
      rw [hdaEq] at hsurA
      rw [hdbEq] at hsurB
      omega

namespace OrderedEdgeColoring

theorem commonRetainedInactive_card_le_projectedFree_left
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (commonRetainedInactive C u v).card ≤ projectedFree C u := by
  classical
  rw [commonRetainedInactive_card]
  unfold projectedFree
  have hsub :
      retainedActive C u ⊆
        retainedActive C u ∪ retainedActive C v :=
    Finset.subset_union_left
  have hcard :=
    Finset.card_le_card hsub
  have huN :
      (retainedActive C u).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C u)
  have huvN :
      (retainedActive C u ∪ retainedActive C v).card ≤ n := by
    simpa using
      Finset.card_le_univ
        (retainedActive C u ∪ retainedActive C v)
  omega

theorem commonRetainedInactive_card_le_projectedFree_right
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (commonRetainedInactive C u v).card ≤ projectedFree C v := by
  classical
  rw [commonRetainedInactive_card]
  unfold projectedFree
  have hsub :
      retainedActive C v ⊆
        retainedActive C u ∪ retainedActive C v :=
    Finset.subset_union_right
  have hcard :=
    Finset.card_le_card hsub
  have hvN :
      (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  have huvN :
      (retainedActive C u ∪ retainedActive C v).card ≤ n := by
    simpa using
      Finset.card_le_univ
        (retainedActive C u ∪ retainedActive C v)
  omega

/-- If both endpoints have strict projected slack, their profile surplus pays
the complete pairwise overlap cube. -/
theorem overlap_card_le_pair_surplus_of_both_strict
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v)
    (huStrict : exponent u < projectedFree C u)
    (hvStrict : exponent v < projectedFree C v) :
    (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
      ≤
    dyadicProfileSurplus exponent (projectedFree C) u +
      dyadicProfileSurplus exponent (projectedFree C) v := by
  rw [retainedCompletionWords_inter_card
      C hbaseU hbaseV]
  unfold dyadicProfileSurplus
  exact pow_le_sum_dyadic_surplus_of_both_lt
    (commonRetainedInactive_card_le_projectedFree_left C u v)
    (commonRetainedInactive_card_le_projectedFree_right C u v)
    huStrict hvStrict

/-- Consequently, an overlap carrier not locally payable by its endpoint
surpluses must have at least one saturated endpoint, provided the one-layer
residual-active budget gives exponent <= projectedFree. -/
theorem overlap_unpaid_implies_endpoint_saturated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {word : Fin n → Bool}
    (hoverlap : word ∈ overlapCompletionWords C)
    {u v : V}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunpaid :
      ¬ ((retainedCompletionWords C u ∩
          retainedCompletionWords C v).card
        ≤
        dyadicProfileSurplus exponent (projectedFree C) u +
          dyadicProfileSurplus exponent (projectedFree C) v)) :
    exponent u = projectedFree C u ∨
      exponent v = projectedFree C v := by
  have hresU :=
    residual_mem_active_of_overlapWord_member
      C hoverlap huWord
  have hresV :=
    residual_mem_active_of_overlapWord_member
      C hoverlap hvWord
  have huLe :=
    exponent_le_projectedFree_of_residual_mem
      C exponent hexp honeLoss hresU
  have hvLe :=
    exponent_le_projectedFree_of_residual_mem
      C exponent hexp honeLoss hresV
  by_contra hsat
  push_neg at hsat
  have huStrict : exponent u < projectedFree C u := by
    omega
  have hvStrict : exponent v < projectedFree C v := by
    omega
  exact hunpaid
    (overlap_card_le_pair_surplus_of_both_strict
      C exponent huWord hvWord huStrict hvStrict)

#print axioms half_pow_le_dyadic_surplus_of_lt
#print axioms pow_le_sum_dyadic_surplus_of_both_lt
#print axioms overlap_card_le_pair_surplus_of_both_strict
#print axioms overlap_unpaid_implies_endpoint_saturated

end OrderedEdgeColoring
end JSP000404Research
