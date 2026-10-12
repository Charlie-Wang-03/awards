import JSP000404Research.ResidualTerminalHardCarrierPartition
import JSP000404Research.ResidualTerminalDoubleSaturatedHard
import Mathlib.Tactic

/-!
# Exact lower-branch net-payment frontier after terminal hard-face partition

On the genuine one-layer residual budget, the remaining hard mass
is EXACTLY two terms:
  (1) transportable hard Boolean-word mass;
  (2) the sum of the upper target weights of doubly saturated rigid pairs.

This is not a claim that either term is paid by Boolean holes.
The new final inequality is formally equivalent to the previous
both-mixed-rigid net payment, NOT yet proved geometrically.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Hard-carrier endpoints satisfy projected-free budgets
under the one-layer active budget, since the residual top
colour is active at BOTH endpoints. -/
theorem netRigidHardCarriers_endpoint_budgets_of_oneLayer
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    ∀ p ∈ netRigidHardCarriers C exponent,
      exponent p.1 ≤ projectedFree C p.1 ∧
        exponent p.2 ≤ projectedFree C p.2 := by
  intro p hp
  have hpdata := (mem_netRigidHardCarriers C exponent p).1 hp
  have hhard :=
    ((mem_netUnpaidHardCarrierPairs C exponent p).1 hpdata.1).1
  have hres : p.1 < p.2 ∧ IsResidual C p.1 p.2 :=
    (mem_residualCarrierPairs C p.1 p.2).1
      ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1 hhard).1).1
  have hactive :=
    residualCoord_mem_active_of_isResidual C hres.1 hres.2
  exact ⟨exponent_le_projectedFree_of_residual_mem
      C exponent hexp honeLoss hactive.1,
    exponent_le_projectedFree_of_residual_mem
      C exponent hexp honeLoss hactive.2⟩

/-- Exact global word-cardinal identity in the one-layer regime:
the terminal rigid obstruction costs one dyadic target weight
at the upper endpoint of each surviving rigid pair. -/
theorem remainingUnpaidHard_card_eq_transportable_add_terminal_targets
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (remainingUnpaidHardAfterMixedRigidWords C exponent).card =
      (netTransportableHardWords C exponent).card +
        (∑ p ∈ netRigidHardCarriers C exponent,
          2 ^ exponent p.2) := by
  rw [remainingUnpaidHard_card_eq_transportable_add_rigid]
  rw [netRigidHardWords_card_eq_sum_upper_target C exponent
    (netRigidHardCarriers_endpoint_budgets_of_oneLayer
      C exponent hexp honeLoss)]

/-- EXACT equivalence: the old global net payment is the same
as a five-term frontier, with the rigid portion made explicit.
In the latter frontier every still-unpaid rigid face has both
endpoints saturated, and its entire mass is counted ONCE. -/
theorem completion_defect_payment_iff_after_terminal_hard_split
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    ((softOverlapCompletionWords C).card +
      (remainingUnpaidHardAfterMixedRigidWords C exponent).card +
      (∑ p ∈ ascendingUnpaidRigidCarriers C exponent, 2 ^ exponent p.1) +
      (∑ p ∈ descendingUnpaidRigidCarriers C exponent, 2 ^ exponent p.2) +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
        (2 ^ n - (coveredCompletionWords C).card) +
          (totalDyadicProfileSurplus exponent (projectedFree C) -
            (surplusPaidHardOverlapWords C exponent).card -
            (∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
              dyadicProfileSurplus exponent (projectedFree C) p.1) -
            (∑ p ∈ descendingUnpaidRigidCarriers C exponent,
              dyadicProfileSurplus exponent (projectedFree C) p.2)))
    ↔
    ((softOverlapCompletionWords C).card +
      (netTransportableHardWords C exponent).card +
      (∑ p ∈ netRigidHardCarriers C exponent, 2 ^ exponent p.2) +
      (∑ p ∈ ascendingUnpaidRigidCarriers C exponent, 2 ^ exponent p.1) +
      (∑ p ∈ descendingUnpaidRigidCarriers C exponent, 2 ^ exponent p.2) +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
        (2 ^ n - (coveredCompletionWords C).card) +
          (totalDyadicProfileSurplus exponent (projectedFree C) -
            (surplusPaidHardOverlapWords C exponent).card -
            (∑ p ∈ ascendingUnpaidRigidCarriers C exponent,
              dyadicProfileSurplus exponent (projectedFree C) p.1) -
            (∑ p ∈ descendingUnpaidRigidCarriers C exponent,
              dyadicProfileSurplus exponent (projectedFree C) p.2))) := by
  rw [remainingUnpaidHard_card_eq_transportable_add_terminal_targets
    C exponent hexp honeLoss]
  simp only [Nat.add_assoc]

/-- Upper bound on the genuine last hard Boolean mass with the
terminal rigid dyadic obstruction isolated; the transport bound
uses singleton and soft COVERED destinations, not holes. -/
theorem remainingUnpaidHard_card_le_singleton_soft_add_terminal_targets
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (remainingUnpaidHardAfterMixedRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card +
          (∑ p ∈ netRigidHardCarriers C exponent, 2 ^ exponent p.2) := by
  have h := remainingUnpaidHard_card_eq_transportable_add_terminal_targets
    C exponent hexp honeLoss
  have htransport :=
    netTransportableHardWords_card_le_singleton_add_soft C exponent
  omega

#print axioms netRigidHardCarriers_endpoint_budgets_of_oneLayer
#print axioms remainingUnpaidHard_card_eq_transportable_add_terminal_targets
#print axioms completion_defect_payment_iff_after_terminal_hard_split
#print axioms remainingUnpaidHard_card_le_singleton_soft_add_terminal_targets

end OrderedEdgeColoring
end JSP000404Research
