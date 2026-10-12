import JSP000404Research.ResidualTerminalTwinStrictPartition
import Mathlib.Tactic

/-!
# The final planar obstruction after fully global reverse transport:
# distinguish BOTH movable classes and only TWIN immobile rigid debt.

Under a genuine one-layer residual budget, the previous terminal
rigid target-weight sum equals the exactly counted strictly-descending
reversibly transportable Boolean faces PLUS the upper target-weight
sum of equal-exponent twins.

The resulting six-source net inequality is EXACTLY EQUIVALENT to the
previous five-source inequality and hence to the lower-branch bound.
It remains an UNPROVED payment obligation.

Caution: the forward and reverse maps are each globally injective
into COVERED singleton/soft sinks, but the union of their images is
not certified injective. We do not charge those sinks twice or count
them as true Boolean holes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Refine the dyadic terminal rigid target mass to the strict
reverse-mobile count and the truly twin rigid dyadic debts. -/
theorem terminal_rigid_target_sum_eq_strict_words_add_twins
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (∑ p ∈ netRigidHardCarriers C exponent, 2 ^ exponent p.2) =
      (netStrictDescentRigidWords C exponent).card +
        (∑ p ∈ netTwinRigidCarriers C exponent,
          2 ^ exponent p.2) := by
  have hold := remainingUnpaidHard_card_eq_transportable_add_terminal_targets
    C exponent hexp honeLoss
  have hnew := remainingUnpaidHard_card_eq_transport_strict_twin
    C exponent hexp honeLoss
  have htwin := netTwinRigidWords_card_eq_dyadic_target_sum
    C exponent hexp honeLoss
  omega

/-- Exact terminal-net inequality equivalence AFTER splitting
the residual rigid target sum into reverse-mobile and true twins.
No extra hypothesis beyond the already verified one-layer budget. -/
theorem completion_defect_payment_iff_after_terminal_twin_split
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
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
              dyadicProfileSurplus exponent (projectedFree C) p.2)))
    ↔
    ((softOverlapCompletionWords C).card +
      (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card +
      (∑ p ∈ netTwinRigidCarriers C exponent, 2 ^ exponent p.2) +
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
  rw [terminal_rigid_target_sum_eq_strict_words_add_twins
    C exponent hexp honeLoss]
  simp only [Nat.add_assoc]

#print axioms terminal_rigid_target_sum_eq_strict_words_add_twins
#print axioms completion_defect_payment_iff_after_terminal_twin_split

end OrderedEdgeColoring
end JSP000404Research
