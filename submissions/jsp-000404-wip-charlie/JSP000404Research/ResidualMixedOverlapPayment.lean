
import JSP000404Research.ResidualMixedOverlapRigidity
import JSP000404Research.ResidualExactBudget
import Mathlib.Tactic

/-!
# Exact remaining cost of a mixed unpaid overlap

Consider a projected overlap carrier u,v.

Assume u is projected-budget saturated,

  exponent(u) = projectedFree(u),

while v is strict,

  exponent(v) < projectedFree(v).

If the overlap is not already paid by the profile surplus of v alone, then
ResidualMixedOverlapRigidity forces

  card(commonInactive(u,v)) = projectedFree(v).

Hence the pairwise overlap cube has exactly the full size of Q_v:

  card(Q_u inter Q_v) = 2^projectedFree(v).

The same equality and saturation at u imply

  projectedFree(v) <= projectedFree(u) = exponent(u),

while strictness at v gives

  exponent(v) < projectedFree(v).

Therefore

  exponent(v) < exponent(u).

Finally

  2^projectedFree(v)
    = (2^projectedFree(v)-2^exponent(v)) + 2^exponent(v).

So after spending all profile surplus of the strict endpoint, the exact
unpaid remainder of this mixed carrier is one old target weight of the
strict endpoint, and that endpoint has strictly smaller exponent than the
saturated endpoint.

This is the bridge from mixed residual overlap to exponent-descent/deletion
arguments.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedFree_right_le_left_of_mixed_unpaid
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
    projectedFree C v ≤ projectedFree C u := by
  have hfull :=
    unpaid_by_strict_endpoint_implies_full_common_inactive_dimension
      C exponent hbaseU hbaseV hvStrict hunpaid
  have hle :=
    commonRetainedInactive_card_le_projectedFree_left
      C u v
  omega

/-- Mixed unpaid carriers point strictly downward in the target exponent from
the saturated endpoint to the strict endpoint. -/
theorem exponent_strictly_descends_on_mixed_unpaid
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvStrict : exponent v < projectedFree C v)
    (hunpaid :
      ¬ ((retainedCompletionWords C u ∩
          retainedCompletionWords C v).card
        ≤
        dyadicProfileSurplus exponent (projectedFree C) v)) :
    exponent v < exponent u := by
  have hfree :=
    projectedFree_right_le_left_of_mixed_unpaid
      C exponent hbaseU hbaseV hvStrict hunpaid
  rw [huSat]
  exact hvStrict.trans_le hfree

/-- In the mixed unpaid case, the overlap cube is exactly the entire strict
endpoint completion cube in cardinality. -/
theorem mixed_unpaid_overlap_card_eq_strict_cube_card
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
    (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card =
      (retainedCompletionWords C v).card := by
  have hfull :=
    unpaid_by_strict_endpoint_implies_full_common_inactive_dimension
      C exponent hbaseU hbaseV hvStrict hunpaid
  rw [retainedCompletionWords_inter_card
      C hbaseU hbaseV,
      retainedCompletionWords_card,
      hfull]

/-- Exact arithmetic decomposition: strict surplus plus one strict target
weight equals the whole mixed overlap cube. -/
theorem mixed_unpaid_overlap_card_eq_surplus_add_target
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
    (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card =
      dyadicProfileSurplus exponent (projectedFree C) v +
        2 ^ exponent v := by
  rw [mixed_unpaid_overlap_card_eq_strict_cube_card
      C exponent hbaseU hbaseV hvStrict hunpaid,
      retainedCompletionWords_card]
  unfold dyadicProfileSurplus
  have hp :
      2 ^ exponent v ≤ 2 ^ projectedFree C v :=
    Nat.pow_le_pow_right
      (by norm_num : 0 < 2)
      (Nat.le_of_lt hvStrict)
  omega

/-- Symmetric orientation: if v is saturated and u strict, the strict lower
endpoint has smaller target exponent. -/
theorem exponent_strictly_descends_on_mixed_unpaid_symm
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v)
    (hvSat : ExactProjectedBudget C exponent v)
    (huStrict : exponent u < projectedFree C u)
    (hunpaid :
      ¬ ((retainedCompletionWords C u ∩
          retainedCompletionWords C v).card
        ≤
        dyadicProfileSurplus exponent (projectedFree C) u)) :
    exponent u < exponent v := by
  have hfree :
      projectedFree C u ≤ projectedFree C v := by
    have hfull :=
      unpaid_by_strict_endpoint_implies_full_common_inactive_dimension
        C exponent hbaseV hbaseU huStrict
        (by
          simpa [Finset.inter_comm, Nat.add_comm] using hunpaid)
    have hle :=
      commonRetainedInactive_card_le_projectedFree_left
        C v u
    simpa [commonRetainedInactive, Finset.union_comm] using
      (show projectedFree C u ≤ projectedFree C v by omega)
  rw [hvSat]
  exact huStrict.trans_le hfree

#print axioms projectedFree_right_le_left_of_mixed_unpaid
#print axioms exponent_strictly_descends_on_mixed_unpaid
#print axioms mixed_unpaid_overlap_card_eq_surplus_add_target

end OrderedEdgeColoring
end JSP000404Research
