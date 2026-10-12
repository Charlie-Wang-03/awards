import JSP000404Research.ResidualBridgeReverseLowerSharedCapacity
import Mathlib.Tactic

/-!
# EXACT lower dyadic capacity for bridge-soft PLUS reverse strict source

The strict-descending terminal rigid hard carriers are a VERTEX
matching, and a retained completion word in two distinct LOWER
residual cubes would force the two lower endpoints to coincide.
Thus their entire lower cubes are globally disjoint.

At either endpoint of a true terminal rigid carrier the one-layer
active budget is saturated, including at its lower endpoint:
  projectedFree C lower = exponent lower.

Consequently the sum of the lower cube capacities equals the
total exact finite union size:
  card(strictRigidLowerCapacityWords)
     = SUM_strict q, 2 ^ exponent(q.lower).

Combining the separately verified SOFT/HARD disjointness and shared
lower-cube union containment yields the new global bound

  card(bridgeSoftWords) + card(reverseStrictRigidHardWords)
     <= SUM_strict q, 2 ^ exponent(q.lower).

The bridge candidate mass is thereby limited by the GAPS between
strict rigid lower and upper target weights, once strict source
mass is also written as an upper target-weight sum.

No new Hall expansion or true-hole assumption is introduced.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Distinct strict-rigid hard carriers have globally disjoint
LOWER completion cubes; this is stronger than disjoint hard faces. -/
theorem netStrictRigidLowerCubes_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    ((netStrictDescentRigidCarriers C exponent : Finset (V × V)) :
       Set (V × V)).PairwiseDisjoint
      (fun q => retainedCompletionWords C q.1) := by
  classical
  intro p hp q hq hpq
  rw [Finset.disjoint_left]
  intro word hpword hqword
  have hp' : p ∈ netStrictDescentRigidCarriers C exponent := by
    simpa using hp
  have hq' : q ∈ netStrictDescentRigidCarriers C exponent := by
    simpa using hq
  have hpNet := ((mem_netStrictDescentRigidCarriers C exponent p).1 hp').1
  have hqNet := ((mem_netStrictDescentRigidCarriers C exponent q).1 hq').1
  have hpData := (mem_netUnpaidHardCarrierPairs C exponent p).1
    ((mem_netRigidHardCarriers C exponent p).1 hpNet).1
  have hqData := (mem_netUnpaidHardCarrierPairs C exponent q).1
    ((mem_netRigidHardCarriers C exponent q).1 hqNet).1
  have hpHard := hpData.1
  have hqHard := hqData.1
  have hpRes : p.1 < p.2 ∧ IsResidual C p.1 p.2 :=
    (mem_residualCarrierPairs C p.1 p.2).1
      ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1 hpHard).1).1
  have hqRes : q.1 < q.2 ∧ IsResidual C q.1 q.2 :=
    (mem_residualCarrierPairs C q.1 q.2).1
      ((mem_overlapCarrierPairs C q).1
        ((mem_hardOverlapCarrierPairs C q).1 hqHard).1).1
  have hlower : p.1 = q.1 :=
    residual_lower_completion_word_unique C
      hpRes.1 hqRes.1 hpRes.2 hqRes.2 hpword hqword
  have hpair : p = q :=
    hard_carrier_shared_endpoint_implies_same_pair
      C hpHard hqHard (Or.inl hlower)
  exact hpq hpair

/-- Exact disjoint lower-cube cardinality in terms of
projected-free dimensions, without any profile budget. -/
theorem netStrictRigidLowerCubes_card_eq_projected_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (netStrictRigidLowerCapacityWords C exponent).card =
      ∑ q ∈ netStrictDescentRigidCarriers C exponent,
        2 ^ projectedFree C q.1 := by
  classical
  unfold netStrictRigidLowerCapacityWords
  rw [Finset.card_biUnion
    (netStrictRigidLowerCubes_pairwiseDisjoint C exponent)]
  apply Finset.sum_congr rfl
  intro q hq
  exact retainedCompletionWords_card C q.1

/-- In the standard one-layer residual profile, every strict-rigid
hard carrier has a SATURATED lower endpoint. -/
theorem netStrictRigidLower_projectedFree_eq_exponent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    {q : V × V}
    (hq : q ∈ netStrictDescentRigidCarriers C exponent) :
    projectedFree C q.1 = exponent q.1 := by
  have hqNet := ((mem_netStrictDescentRigidCarriers C exponent q).1 hq).1
  have hqRigid := (mem_netRigidHardCarriers C exponent q).1 hqNet
  have hqData := (mem_netUnpaidHardCarrierPairs C exponent q).1
    hqRigid.1
  have hrig : q ∈ rigidHardOverlapCarrierPairs C :=
    (mem_rigidHardOverlapCarrierPairs C q).2
      ⟨hqData.1,hqRigid.2⟩
  have hbudget :=
    netRigidHardCarriers_endpoint_budgets_of_oneLayer
      C exponent hexp honeLoss q hqNet
  have hsat :=
    terminal_rigid_carrier_both_saturated_without_word
      C exponent hrig hqData.2.1 hqData.2.2.1 hqData.2.2.2
        hbudget.1 hbudget.2
  exact hsat.1.symm

/-- EXACT available lower-cube dyadic capacity for all reverse
strict-rigid hard carriers under the genuine one-layer budget. -/
theorem netStrictRigidLowerCubes_card_eq_lower_target_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (netStrictRigidLowerCapacityWords C exponent).card =
      ∑ q ∈ netStrictDescentRigidCarriers C exponent,
        2 ^ exponent q.1 := by
  rw [netStrictRigidLowerCubes_card_eq_projected_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [netStrictRigidLower_projectedFree_eq_exponent
    C exponent hexp honeLoss hq]

/-- The POTENTIAL bridge-soft collision face pool plus the ENTIRE
reverse strict-rigid hard source mass fits inside the dyadic SUM
of lower endpoints. This is a genuine joint finite mass bound. -/
theorem bridge_soft_add_reverse_strict_le_lower_target_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (forwardReverseBridgeSoftWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤
        ∑ q ∈ netStrictDescentRigidCarriers C exponent,
          2 ^ exponent q.1 := by
  rw [← netStrictRigidLowerCubes_card_eq_lower_target_sum
    C exponent hexp honeLoss]
  exact bridge_soft_add_reverse_strict_le_lower_cubes C exponent

#print axioms netStrictRigidLowerCubes_pairwiseDisjoint
#print axioms netStrictRigidLowerCubes_card_eq_projected_sum
#print axioms netStrictRigidLower_projectedFree_eq_exponent
#print axioms netStrictRigidLowerCubes_card_eq_lower_target_sum
#print axioms bridge_soft_add_reverse_strict_le_lower_target_sum

end OrderedEdgeColoring
end JSP000404Research
