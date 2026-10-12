import JSP000404Research.ResidualBridgeReverseLowerDyadicBudget
import Mathlib.Tactic

/-!
# Candidate bridge-soft collision mass is paid by STRICT RIGID DIMENSION DESCENT

The exact entire strict-descending rigid hard source-face mass is
  SUM_(q strict) 2 ^ exponent(q.upper)
under the previously verified one-layer double saturation.

We now have the SHARED lower-cube bound
  bridgeSoftMass + strictSourceMass <= SUM_(q strict) 2 ^ exponent(q.lower).

Therefore the full POSSIBLE forward/reverse collision pool satisfies
  bridgeSoftMass <=
      (SUM_strict 2 ^ exponent(lower))
    - (SUM_strict 2 ^ exponent(upper)).

This is an unconditional quantitative DIMENSION DESCENT gap bound,
distinct from and NOT equal to an unreserved dyadic profile surplus:
both endpoints of each strict rigid pair have ZERO LOCAL PROFILE
SURPLUS. Do not transfer this gap directly to the TRUE-HOLE payment
without a new mathematically proved global allocation.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem netStrictDescentRigidWords_card_eq_upper_target_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (netStrictDescentRigidWords C exponent).card =
      ∑ q ∈ netStrictDescentRigidCarriers C exponent,
        2 ^ exponent q.2 := by
  classical
  have hpair :
      ((netStrictDescentRigidCarriers C exponent : Finset (V × V)) :
        Set (V × V)).PairwiseDisjoint (carrierOverlapWords C) := by
    intro p hp q hq hpq
    apply overlapCarrierWords_pairwiseDisjoint C
    · have hp' : p ∈ netStrictDescentRigidCarriers C exponent := by
        simpa using hp
      have hnet := ((mem_netStrictDescentRigidCarriers
        C exponent p).1 hp').1
      have hhard := ((mem_netUnpaidHardCarrierPairs C exponent p).1
        ((mem_netRigidHardCarriers C exponent p).1 hnet).1).1
      exact ((mem_hardOverlapCarrierPairs C p).1 hhard).1
    · have hq' : q ∈ netStrictDescentRigidCarriers C exponent := by
        simpa using hq
      have hnet := ((mem_netStrictDescentRigidCarriers
        C exponent q).1 hq').1
      have hhard := ((mem_netUnpaidHardCarrierPairs C exponent q).1
        ((mem_netRigidHardCarriers C exponent q).1 hnet).1).1
      exact ((mem_hardOverlapCarrierPairs C q).1 hhard).1
    · exact hpq
  unfold netStrictDescentRigidWords
  rw [Finset.card_biUnion hpair]
  apply Finset.sum_congr rfl
  intro q hq
  have hqNet := ((mem_netStrictDescentRigidCarriers C exponent q).1 hq).1
  have hqRigid := (mem_netRigidHardCarriers C exponent q).1 hqNet
  have hqData := (mem_netUnpaidHardCarrierPairs C exponent q).1
    hqRigid.1
  have hrig : q ∈ rigidHardOverlapCarrierPairs C :=
    (mem_rigidHardOverlapCarrierPairs C q).2
      ⟨hqData.1,hqRigid.2⟩
  have hb := netRigidHardCarriers_endpoint_budgets_of_oneLayer
    C exponent hexp honeLoss q hqNet
  exact (terminal_rigid_carrier_mass_and_zero_surplus_without_word
    C exponent hrig hqData.2.1 hqData.2.2.1 hqData.2.2.2
      hb.1 hb.2).1

/-- The FULL candidate cross-transport soft-bridge pool is bounded by
the STRICT DESCENT gap of lower vs upper terminal rigid target weights.
This gap is a dimension-budget difference, NOT surplus available to
the original JSP net-payment inequality. -/
theorem forwardReverseBridgeSoftWords_le_strict_dyadic_descent_gap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (forwardReverseBridgeSoftWords C exponent).card ≤
      (∑ q ∈ netStrictDescentRigidCarriers C exponent,
        2 ^ exponent q.1) -
      (∑ q ∈ netStrictDescentRigidCarriers C exponent,
        2 ^ exponent q.2) := by
  have hjoint := bridge_soft_add_reverse_strict_le_lower_target_sum
    C exponent hexp honeLoss
  rw [netStrictDescentRigidWords_card_eq_upper_target_sum
    C exponent hexp honeLoss] at hjoint
  omega

/-- Pair the exact SOFT bridge face dyadic sum with the exact
strict-rigid UP-TO-DOWN dyadic dimension descent capacity. -/
theorem bridge_soft_dyadic_carrier_mass_le_strict_target_gap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (∑ e ∈ forwardReverseBridgeSoftCarriers C exponent,
      2 ^ (commonRetainedInactive C e.1 e.2).card) ≤
        (∑ q ∈ netStrictDescentRigidCarriers C exponent,
          2 ^ exponent q.1) -
        (∑ q ∈ netStrictDescentRigidCarriers C exponent,
          2 ^ exponent q.2) := by
  rw [← forwardReverseBridgeSoftWords_card_eq_dyadic_sum]
  exact forwardReverseBridgeSoftWords_le_strict_dyadic_descent_gap
    C exponent hexp honeLoss

#print axioms netStrictDescentRigidWords_card_eq_upper_target_sum
#print axioms forwardReverseBridgeSoftWords_le_strict_dyadic_descent_gap
#print axioms bridge_soft_dyadic_carrier_mass_le_strict_target_gap

end OrderedEdgeColoring
end JSP000404Research
