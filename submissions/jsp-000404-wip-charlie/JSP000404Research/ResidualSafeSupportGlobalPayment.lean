import JSP000404Research.ResidualSafeSupportGlobal
import JSP000404Research.ResidualOverlapDimension
import JSP000404Research.ResidualExactBudget
import Mathlib.Tactic

/-!
# Global half-weight payment for support-unsafe saturated overlaps

A support-unsafe overlap carrier u<v has overlap mass

  2 ^ d,  d = card(commonInactiveRetained C u v).

If both endpoints are exact projected-budget saturated, the common-inactive
coordinates are free at each endpoint, so

  d <= exponent(u),  d <= exponent(v).

Hence

  2 * 2^d <= 2^exponent(u) + 2^exponent(v).

Support-unsafe carriers form a matching, so their endpoint sets are globally
disjoint.  Summing the pairwise estimate charges every support-unsafe overlap
cube to at most one half of the target weight of its two endpoints.

This removes the entire no-active-safe common-inactive saturated subtype from
the global Hall problem at the level of target-weight accounting.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

noncomputable def supportUnsafeSaturatedCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Finset (V × V) := by
  classical
  exact (supportUnsafeOverlapCarrierPairs C).filter fun e =>
    ExactProjectedBudget C exponent e.1 ∧
      ExactProjectedBudget C exponent e.2

@[simp] theorem mem_supportUnsafeSaturatedCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (u v : V) :
    (u,v) ∈ supportUnsafeSaturatedCarrierPairs C exponent ↔
      (u,v) ∈ supportUnsafeOverlapCarrierPairs C ∧
      ExactProjectedBudget C exponent u ∧
      ExactProjectedBudget C exponent v := by
  classical
  simp [supportUnsafeSaturatedCarrierPairs]

theorem commonInactive_card_le_exponent_left_of_saturated
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (huSat : ExactProjectedBudget C exponent u) :
    (commonInactiveRetained C u v).card ≤ exponent u := by
  have hsub :
      commonInactiveRetained C u v ⊆ retainedInactive C u := by
    intro c hc
    exact (mem_retainedInactive C u c).2
      ((mem_commonInactiveRetained C u v c).1 hc).1
  have hcard := Finset.card_le_card hsub
  rw [retainedInactive_card, ← huSat] at hcard
  exact hcard

theorem commonInactive_card_le_exponent_right_of_saturated
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (hvSat : ExactProjectedBudget C exponent v) :
    (commonInactiveRetained C u v).card ≤ exponent v := by
  have hsub :
      commonInactiveRetained C u v ⊆ retainedInactive C v := by
    intro c hc
    exact (mem_retainedInactive C v c).2
      ((mem_commonInactiveRetained C u v c).1 hc).2
  have hcard := Finset.card_le_card hsub
  rw [retainedInactive_card, ← hvSat] at hcard
  exact hcard

theorem two_mul_overlap_mass_le_endpoint_weight_of_supportUnsafe_saturated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v) :
    2 *
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
      ≤
    2 ^ exponent u + 2 ^ exponent v := by
  rw [retainedCompletionWords_inter_card_eq_pow_commonInactive
      C hbaseU hbaseV]
  have huLe :=
    commonInactive_card_le_exponent_left_of_saturated
      C exponent huSat
  have hvLe :=
    commonInactive_card_le_exponent_right_of_saturated
      C exponent hvSat
  have hpowU :
      2 ^ (commonInactiveRetained C u v).card ≤
        2 ^ exponent u :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) huLe
  have hpowV :
      2 ^ (commonInactiveRetained C u v).card ≤
        2 ^ exponent v :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hvLe
  omega

noncomputable def supportUnsafeSaturatedEndpointVertices
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset V := by
  classical
  exact (supportUnsafeSaturatedCarrierPairs C exponent).biUnion
    (fun e => {e.1,e.2})

theorem supportUnsafeSaturatedCarrier_endpoint_sets_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    ((supportUnsafeSaturatedCarrierPairs C exponent :
        Finset (V × V)) : Set (V × V)).PairwiseDisjoint
      (fun e => ({e.1,e.2} : Finset V)) := by
  intro e he f hf hef
  classical
  rw [Finset.disjoint_left]
  intro x hxe hxf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxe hxf
  have heBase :
      e ∈ supportUnsafeOverlapCarrierPairs C :=
    ((mem_supportUnsafeSaturatedCarrierPairs
      C exponent e.1 e.2).1 he).1
  have hfBase :
      f ∈ supportUnsafeOverlapCarrierPairs C :=
    ((mem_supportUnsafeSaturatedCarrierPairs
      C exponent f.1 f.2).1 hf).1
  have huniq :=
    supportUnsafeOverlapCarrierPairs_endpoint_unique
      C heBase hfBase hef
  rcases hxe with rfl | rfl <;>
    rcases hxf with rfl | rfl
  · exact huniq.1 rfl
  · exact huniq.2.1 rfl
  · exact huniq.2.2.1 rfl
  · exact huniq.2.2.2 rfl

theorem supportUnsafeSaturatedEndpoint_weight_eq_pair_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (∑ v ∈ supportUnsafeSaturatedEndpointVertices C exponent,
        2 ^ exponent v)
      =
    ∑ e ∈ supportUnsafeSaturatedCarrierPairs C exponent,
      (2 ^ exponent e.1 + 2 ^ exponent e.2) := by
  classical
  unfold supportUnsafeSaturatedEndpointVertices
  rw [Finset.sum_biUnion
    (supportUnsafeSaturatedCarrier_endpoint_sets_pairwiseDisjoint
      C exponent)]
  apply Finset.sum_congr rfl
  intro e he
  have hne :
      e.1 ≠ e.2 := by
    have hbase :=
      ((mem_supportUnsafeSaturatedCarrierPairs
        C exponent e.1 e.2).1 he).1
    exact ne_of_lt
      ((mem_supportUnsafeOverlapCarrierPairs
        C e.1 e.2).1 hbase).1
  simp [hne]

theorem two_mul_supportUnsafeSaturated_overlap_mass_le_endpoint_weight
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    2 *
      (∑ e ∈ supportUnsafeSaturatedCarrierPairs C exponent,
        (carrierOverlapWords C e).card)
      ≤
    ∑ v ∈ supportUnsafeSaturatedEndpointVertices C exponent,
      2 ^ exponent v := by
  classical
  rw [supportUnsafeSaturatedEndpoint_weight_eq_pair_sum
    C exponent]
  rw [← Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have hdata :=
    (mem_supportUnsafeSaturatedCarrierPairs
      C exponent e.1 e.2).1 he
  have hoverlap :=
    (mem_supportUnsafeOverlapCarrierPairs
      C e.1 e.2).1 hdata.1
  obtain ⟨base,hbaseU,hbaseV⟩ := hoverlap.2.2
  simpa [carrierOverlapWords] using
    two_mul_overlap_mass_le_endpoint_weight_of_supportUnsafe_saturated
      C exponent hbaseU hbaseV hdata.2.1 hdata.2.2

theorem two_mul_supportUnsafeSaturated_overlap_mass_le_total_weight
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    2 *
      (∑ e ∈ supportUnsafeSaturatedCarrierPairs C exponent,
        (carrierOverlapWords C e).card)
      ≤
    ∑ v : V, 2 ^ exponent v := by
  have hpair :=
    two_mul_supportUnsafeSaturated_overlap_mass_le_endpoint_weight
      C exponent
  have hsub :
      supportUnsafeSaturatedEndpointVertices C exponent ⊆
        (Finset.univ : Finset V) :=
    Finset.subset_univ _
  have htotal :
      (∑ v ∈ supportUnsafeSaturatedEndpointVertices C exponent,
          2 ^ exponent v)
        ≤
      ∑ v ∈ (Finset.univ : Finset V), 2 ^ exponent v :=
    Finset.sum_le_sum_of_subset hsub
  simpa using hpair.trans htotal

#print axioms supportUnsafeSaturatedCarrier_endpoint_sets_pairwiseDisjoint
#print axioms two_mul_supportUnsafeSaturated_overlap_mass_le_endpoint_weight
#print axioms two_mul_supportUnsafeSaturated_overlap_mass_le_total_weight

end OrderedEdgeColoring
end JSP000404Research
