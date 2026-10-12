import JSP000404Research.ResidualForwardReverseBridgeCapacity
import Mathlib.Tactic

/-!
# Exact dyadic mass of the only possible opposite-transport bridge faces

The forward/reverse global sink collision pool is supported on a
canonical set of SOFT residual bridge carriers (reverseLower,forwardUpper).

Different carrier overlap faces are globally disjoint by the
at-most-two completion-fibre property and unique ordered residual
pair ownership. Each such carrier face has EXACT size

    2 ^ card(commonRetainedInactive C lower upper).

This supplies a completely explicit weighted geometric frontier:

  fullForwardMass + reverseStrictMass
     <= singletonMass + softMass
       + SUM_(bridgeSoftCarrier p) 2^card(commonInactive(p)).

The sum is a CERTIFIED upper bound on possible cross-map collisions,
not an equality with their actual intersection; collisions may be
absent even when an admissible bridge face exists.

Do not confuse these already-covered faces with TRUE Boolean holes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem forwardReverseBridgeSoftWords_card_eq_dyadic_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (forwardReverseBridgeSoftWords C exponent).card =
      ∑ p ∈ forwardReverseBridgeSoftCarriers C exponent,
        2 ^ (commonRetainedInactive C p.1 p.2).card := by
  classical
  have hpair :
      ((forwardReverseBridgeSoftCarriers C exponent : Finset (V × V)) :
        Set (V × V)).PairwiseDisjoint (carrierOverlapWords C) := by
    intro p hp q hq hpq
    apply overlapCarrierWords_pairwiseDisjoint C
    · have hp' : p ∈ forwardReverseBridgeSoftCarriers C exponent := by
        simpa using hp
      have hsoft := (Finset.mem_filter.mp hp').1
      exact ((mem_softOverlapCarrierPairs C p).1 hsoft).1
    · have hq' : q ∈ forwardReverseBridgeSoftCarriers C exponent := by
        simpa using hq
      have hsoft := (Finset.mem_filter.mp hq').1
      exact ((mem_softOverlapCarrierPairs C q).1 hsoft).1
    · exact hpq
  unfold forwardReverseBridgeSoftWords
  rw [Finset.card_biUnion hpair]
  apply Finset.sum_congr rfl
  intro p hp
  have hsoft : p ∈ softOverlapCarrierPairs C :=
    (Finset.mem_filter.mp hp).1
  have hcarrier : p ∈ overlapCarrierPairs C :=
    ((mem_softOverlapCarrierPairs C p).1 hsoft).1
  obtain ⟨word,hword⟩ :=
    ((mem_overlapCarrierPairs C p).1 hcarrier).2
  exact retainedCompletionWords_inter_card
    C (Finset.mem_inter.mp hword).1
      (Finset.mem_inter.mp hword).2

/-- Equivalent fully dyadic version of the joint mobile hard
transport upper bound. -/
theorem forward_reverse_hard_mass_le_singleton_soft_bridge_dyadic
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (transportableHardOverlapCompletionWords C).card +
      (netStrictDescentRigidWords C exponent).card ≤
        (singletonCompletionWords C).card +
          (softOverlapCompletionWords C).card +
          (∑ p ∈ forwardReverseBridgeSoftCarriers C exponent,
            2 ^ (commonRetainedInactive C p.1 p.2).card) := by
  rw [← forwardReverseBridgeSoftWords_card_eq_dyadic_sum]
  exact forward_reverse_hard_mass_le_singleton_soft_bridge
    C exponent hexp honeLoss

/-- Exact remaining hard mass control in terms of a WEIGHTED
SUM over candidate soft bridges plus the true twin target sum. -/
theorem remaining_hard_mass_le_singleton_soft_bridge_dyadic_add_twin
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (remainingUnpaidHardAfterMixedRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card +
        (∑ p ∈ forwardReverseBridgeSoftCarriers C exponent,
          2 ^ (commonRetainedInactive C p.1 p.2).card) +
        (∑ p ∈ netTwinRigidCarriers C exponent,
          2 ^ exponent p.2) := by
  rw [← forwardReverseBridgeSoftWords_card_eq_dyadic_sum]
  exact remaining_hard_mass_le_singleton_soft_bridge_add_twin
    C exponent hexp honeLoss

#print axioms forwardReverseBridgeSoftWords_card_eq_dyadic_sum
#print axioms forward_reverse_hard_mass_le_singleton_soft_bridge_dyadic
#print axioms remaining_hard_mass_le_singleton_soft_bridge_dyadic_add_twin

end OrderedEdgeColoring
end JSP000404Research
