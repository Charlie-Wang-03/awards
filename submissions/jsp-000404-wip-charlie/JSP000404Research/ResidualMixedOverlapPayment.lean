
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
          simpa [Finset.inter_comm] using hunpaid)
    have hle :=
      commonRetainedInactive_card_le_projectedFree_left
        C v u
    omega
  rw [hvSat]
  exact huStrict.trans_le hfree


/-- In the mixed unpaid case, the entire strict endpoint cube is contained in
the saturated-side cube. -/
theorem retainedCompletionWords_subset_of_mixed_unpaid
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
    retainedCompletionWords C v ⊆
      retainedCompletionWords C u := by
  classical
  have hcardEq :=
    mixed_unpaid_overlap_card_eq_strict_cube_card
      C exponent hbaseU hbaseV hvStrict hunpaid
  have hsub :
      retainedCompletionWords C u ∩
          retainedCompletionWords C v
        ⊆ retainedCompletionWords C v :=
    Finset.inter_subset_right
  have hinterEq :
      retainedCompletionWords C u ∩
          retainedCompletionWords C v =
        retainedCompletionWords C v := by
    apply Finset.eq_of_subset_of_card_le hsub
    exact le_of_eq hcardEq.symm
  intro word hw
  have :
      word ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v := by
    rw [hinterEq]
    exact hw
  exact (Finset.mem_inter.mp this).1

/-- Carrier-overlap form: the overlap-word set of a mixed unpaid pair is
exactly the strict endpoint's whole completion cube. -/
theorem carrierOverlapWords_eq_strict_cube_of_mixed_unpaid
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
    carrierOverlapWords C (u,v) =
      retainedCompletionWords C v := by
  unfold carrierOverlapWords
  apply Finset.Subset.antisymm
  · exact Finset.inter_subset_right
  · intro word hw
    exact Finset.mem_inter.mpr
      ⟨retainedCompletionWords_subset_of_mixed_unpaid
          C exponent hbaseU hbaseV hvStrict hunpaid hw,
       hw⟩

/-- A fixed strict endpoint cannot be the strict side of two distinct mixed
unpaid residual carriers. -/
theorem mixed_unpaid_strict_endpoint_carrier_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u₁ u₂ v : V}
    (hu₁v : u₁ < v)
    (hu₂v : u₂ < v)
    (hres₁ : IsResidual C u₁ v)
    (hres₂ : IsResidual C u₂ v)
    {base₁ base₂ : Fin n → Bool}
    (hbase₁U : base₁ ∈ retainedCompletionWords C u₁)
    (hbase₁V : base₁ ∈ retainedCompletionWords C v)
    (hbase₂U : base₂ ∈ retainedCompletionWords C u₂)
    (hbase₂V : base₂ ∈ retainedCompletionWords C v)
    (hvStrict : exponent v < projectedFree C v)
    (hunpaid₁ :
      ¬ ((retainedCompletionWords C u₁ ∩
          retainedCompletionWords C v).card
        ≤
        dyadicProfileSurplus exponent (projectedFree C) v))
    (hunpaid₂ :
      ¬ ((retainedCompletionWords C u₂ ∩
          retainedCompletionWords C v).card
        ≤
        dyadicProfileSurplus exponent (projectedFree C) v)) :
    u₁ = u₂ := by
  classical
  by_contra hne
  have hp₁ :
      (u₁,v) ∈ residualCarrierPairs C :=
    (mem_residualCarrierPairs C u₁ v).2
      ⟨hu₁v, hres₁⟩
  have hp₂ :
      (u₂,v) ∈ residualCarrierPairs C :=
    (mem_residualCarrierPairs C u₂ v).2
      ⟨hu₂v, hres₂⟩
  have hpairs :
      (u₁,v) ≠ (u₂,v) := by
    intro h
    exact hne (congrArg Prod.fst h)
  have hdisj :=
    carrierOverlapWords_pairwiseDisjoint C
      hp₁ hp₂ hpairs
  have hEq₁ :=
    carrierOverlapWords_eq_strict_cube_of_mixed_unpaid
      C exponent hbase₁U hbase₁V hvStrict hunpaid₁
  have hEq₂ :=
    carrierOverlapWords_eq_strict_cube_of_mixed_unpaid
      C exponent hbase₂U hbase₂V hvStrict hunpaid₂
  rw [hEq₁, hEq₂] at hdisj
  have hnonempty :
      (retainedCompletionWords C v).Nonempty :=
    ⟨base₁, hbase₁V⟩
  exact hnonempty.not_disjoint hdisj

/-- Symmetric uniqueness when the strict endpoint is the lower endpoint. -/
theorem mixed_unpaid_strict_lower_carrier_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v₁ v₂ : V}
    (huv₁ : u < v₁)
    (huv₂ : u < v₂)
    (hres₁ : IsResidual C u v₁)
    (hres₂ : IsResidual C u v₂)
    {base₁ base₂ : Fin n → Bool}
    (hbase₁U : base₁ ∈ retainedCompletionWords C u)
    (hbase₁V : base₁ ∈ retainedCompletionWords C v₁)
    (hbase₂U : base₂ ∈ retainedCompletionWords C u)
    (hbase₂V : base₂ ∈ retainedCompletionWords C v₂)
    (huStrict : exponent u < projectedFree C u)
    (hunpaid₁ :
      ¬ ((retainedCompletionWords C u ∩
          retainedCompletionWords C v₁).card
        ≤
        dyadicProfileSurplus exponent (projectedFree C) u))
    (hunpaid₂ :
      ¬ ((retainedCompletionWords C u ∩
          retainedCompletionWords C v₂).card
        ≤
        dyadicProfileSurplus exponent (projectedFree C) u)) :
    v₁ = v₂ := by
  classical
  by_contra hne
  have hp₁ :
      (u,v₁) ∈ residualCarrierPairs C :=
    (mem_residualCarrierPairs C u v₁).2
      ⟨huv₁, hres₁⟩
  have hp₂ :
      (u,v₂) ∈ residualCarrierPairs C :=
    (mem_residualCarrierPairs C u v₂).2
      ⟨huv₂, hres₂⟩
  have hpairs :
      (u,v₁) ≠ (u,v₂) := by
    intro h
    exact hne (congrArg Prod.snd h)
  have hdisj :=
    carrierOverlapWords_pairwiseDisjoint C
      hp₁ hp₂ hpairs
  have hEq₁ :
      carrierOverlapWords C (u,v₁) =
        retainedCompletionWords C u := by
    unfold carrierOverlapWords
    apply Finset.Subset.antisymm
    · exact Finset.inter_subset_left
    · intro word hw
      have hsub :
          retainedCompletionWords C u ⊆
            retainedCompletionWords C v₁ := by
        -- apply the right-endpoint theorem after swapping the two cube roles
        have hcard :
            (retainedCompletionWords C v₁ ∩
                retainedCompletionWords C u).card =
              (retainedCompletionWords C u).card := by
          have h :=
            mixed_unpaid_overlap_card_eq_strict_cube_card
              C exponent hbase₁V hbase₁U huStrict
              (by simpa [Finset.inter_comm] using hunpaid₁)
          exact h
        have hinter :
            retainedCompletionWords C v₁ ∩
                retainedCompletionWords C u =
              retainedCompletionWords C u := by
          apply Finset.eq_of_subset_of_card_le
            Finset.inter_subset_right
          exact le_of_eq hcard.symm
        have hw' :
            word ∈ retainedCompletionWords C v₁ ∩
              retainedCompletionWords C u := by
          rw [hinter]
          exact hw
        exact (Finset.mem_inter.mp hw').1
      exact Finset.mem_inter.mpr ⟨hw, hsub hw⟩
  have hEq₂ :
      carrierOverlapWords C (u,v₂) =
        retainedCompletionWords C u := by
    unfold carrierOverlapWords
    apply Finset.Subset.antisymm
    · exact Finset.inter_subset_left
    · intro word hw
      have hsub :
          retainedCompletionWords C u ⊆
            retainedCompletionWords C v₂ := by
        have hcard :
            (retainedCompletionWords C v₂ ∩
                retainedCompletionWords C u).card =
              (retainedCompletionWords C u).card := by
          exact
            mixed_unpaid_overlap_card_eq_strict_cube_card
              C exponent hbase₂V hbase₂U huStrict
              (by simpa [Finset.inter_comm] using hunpaid₂)
        have hinter :
            retainedCompletionWords C v₂ ∩
                retainedCompletionWords C u =
              retainedCompletionWords C u := by
          apply Finset.eq_of_subset_of_card_le
            Finset.inter_subset_right
          exact le_of_eq hcard.symm
        have hw' :
            word ∈ retainedCompletionWords C v₂ ∩
              retainedCompletionWords C u := by
          rw [hinter]
          exact hw
        exact (Finset.mem_inter.mp hw').1
      exact Finset.mem_inter.mpr ⟨hw, hsub hw⟩
  rw [hEq₁, hEq₂] at hdisj
  have hnonempty :
      (retainedCompletionWords C u).Nonempty :=
    ⟨base₁, hbase₁U⟩
  exact hnonempty.not_disjoint hdisj

#print axioms projectedFree_right_le_left_of_mixed_unpaid
#print axioms exponent_strictly_descends_on_mixed_unpaid
#print axioms mixed_unpaid_overlap_card_eq_surplus_add_target

end OrderedEdgeColoring
end JSP000404Research
