
import JSP000404Research.ResidualOverlapSurplus
import JSP000404Research.ResidualOverlapCube
import Mathlib.Tactic

/-!
# Mixed strict-saturated overlap rigidity

Let u,v carry a common retained completion word and let

  d = card(commonRetainedInactive(u,v)).

Suppose v is strict in the projected profile:

  exponent(v) < projectedFree(v).

Then one strict endpoint alone already pays the complete overlap cube whenever

  d < projectedFree(v).

Indeed the strict dyadic surplus at v is at least

  2^(projectedFree(v)-1),

while d < projectedFree(v) gives

  2^d <= 2^(projectedFree(v)-1).

Therefore a mixed carrier which is not paid by the strict endpoint must satisfy

  d = projectedFree(v).

Since common inactive coordinates are always a subset of v's inactive
coordinates and the two sets now have equal cardinality, they are equal:

  commonRetainedInactive(u,v) = retainedInactive(v).

Equivalently,

  retainedInactive(v) subset retainedInactive(u),

so every free coordinate of the strict endpoint is also free at the other
endpoint.

This is the exact mixed hard-overlap shape.
-/

namespace JSP000404Research

/-- A strict dyadic profile surplus pays any strictly smaller-dimensional
Boolean subcube. -/
theorem pow_le_dyadic_surplus_of_dim_lt
    {d x a : ℕ}
    (hda : d < a)
    (hxa : x < a) :
    2 ^ d ≤ 2 ^ a - 2 ^ x := by
  have hd : d ≤ a - 1 := by omega
  have hp :
      2 ^ d ≤ 2 ^ (a - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hd
  have hsur :=
    half_pow_le_dyadic_surplus_of_lt hxa
  exact hp.trans hsur

namespace OrderedEdgeColoring

/-- If the overlap dimension is strictly below one strict endpoint's free
dimension, that endpoint alone pays the whole pairwise overlap cube. -/
theorem overlap_card_le_one_endpoint_surplus_of_dim_lt
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v)
    (hvStrict : exponent v < projectedFree C v)
    (hdim :
      (commonRetainedInactive C u v).card <
        projectedFree C v) :
    (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
      ≤
    dyadicProfileSurplus exponent (projectedFree C) v := by
  rw [retainedCompletionWords_inter_card
      C hbaseU hbaseV]
  unfold dyadicProfileSurplus
  exact pow_le_dyadic_surplus_of_dim_lt
    hdim hvStrict

/-- An overlap not paid by the strict endpoint must use every free coordinate
of that endpoint. -/
theorem unpaid_by_strict_endpoint_implies_full_common_inactive_dimension
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v)
    (hvStrict : exponent v < projectedFree C v)
    (hunpaid :
      ¬ ((retainedCompletionWords C u ∩
          retainedCompletionWords C v).card
        ≤
        dyadicProfileSurplus exponent (projectedFree C) v)) :
    (commonRetainedInactive C u v).card =
      projectedFree C v := by
  have hle :=
    commonRetainedInactive_card_le_projectedFree_right
      C u v
  by_contra hne
  have hlt :
      (commonRetainedInactive C u v).card <
        projectedFree C v := by
    omega
  exact hunpaid
    (overlap_card_le_one_endpoint_surplus_of_dim_lt
      C exponent hbaseU hbaseV hvStrict hlt)

/-- Full common-inactive dimension forces exact equality with the strict
endpoint's inactive-coordinate set. -/
theorem commonInactive_eq_retainedInactive_right_of_card_eq
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hcard :
      (commonRetainedInactive C u v).card =
        projectedFree C v) :
    commonRetainedInactive C u v =
      retainedInactive C v := by
  classical
  have hsub :
      commonRetainedInactive C u v ⊆
        retainedInactive C v := by
    intro c hc
    exact (mem_retainedInactive C v c).2
      ((mem_commonRetainedInactive C u v c).1 hc).2
  have hcardInactive :
      (retainedInactive C v).card =
        projectedFree C v := by
    rw [retainedInactive_card]
    rfl
  apply Finset.Subset.antisymm hsub
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hcard, hcardInactive]

/-- Set-inclusion form: every free coordinate of the strict endpoint is also
free at the other endpoint. -/
theorem retainedInactive_right_subset_left_of_full_common_dimension
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hcard :
      (commonRetainedInactive C u v).card =
        projectedFree C v) :
    retainedInactive C v ⊆ retainedInactive C u := by
  intro c hc
  have heq :=
    commonInactive_eq_retainedInactive_right_of_card_eq
      C hcard
  have hcCommon :
      c ∈ commonRetainedInactive C u v := by
    rw [heq]
    exact hc
  exact (mem_retainedInactive C u c).2
    ((mem_commonRetainedInactive C u v c).1 hcCommon).1

/-- Main mixed-rigidity package. -/
theorem mixed_unpaid_overlap_forces_free_set_inclusion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v)
    (hvStrict : exponent v < projectedFree C v)
    (hunpaid :
      ¬ ((retainedCompletionWords C u ∩
          retainedCompletionWords C v).card
        ≤
        dyadicProfileSurplus exponent (projectedFree C) v)) :
    retainedInactive C v ⊆ retainedInactive C u := by
  apply retainedInactive_right_subset_left_of_full_common_dimension C
  exact unpaid_by_strict_endpoint_implies_full_common_inactive_dimension
    C exponent hbaseU hbaseV hvStrict hunpaid

#print axioms pow_le_dyadic_surplus_of_dim_lt
#print axioms overlap_card_le_one_endpoint_surplus_of_dim_lt
#print axioms unpaid_by_strict_endpoint_implies_full_common_inactive_dimension
#print axioms commonInactive_eq_retainedInactive_right_of_card_eq
#print axioms mixed_unpaid_overlap_forces_free_set_inclusion

end OrderedEdgeColoring
end JSP000404Research
