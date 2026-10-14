import JSP000404Research.ResidualNetCollisionExactShellColourSlots
import Mathlib.Tactic

/-!
# Certified exact-shell joint capacity and unpaid mobile payment bound

Let B(d) be the ACTUAL-source-compatible double-shell bridge candidates,
and let L*(d), U*(d) be the NEW target-exact lower/upper
endpoint-colour slots. A genuine source fibre for d injects into
each of these three finite candidate pools, giving the joint
per-target MIN capacity. The exact global duplicate-image debt
is bounded by the sum of joint target-capacity excesses.

Finally, combine the verified mobile-source/true-hole/covered/duplicate
accounting with this tighter duplicate upper bound, leaving the
literal global TRUE Boolean holes and the covered diagonal blockers
as distinct, unreused resources.

No step pays covered endpoints from true holes, assumes target
uniqueness under planar AngleCap, or discharges the remaining
six-source global geometric payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Per actual canonical diagonal target, every source is bounded
simultaneously by a certified original soft bridge and by LOWER/UPPER
target-EXACT original flip-colour slots. All three are individually
source-native injections, and the minimum is never weaker than the
previous coarse joint slot bound. -/
theorem net_collision_diagonal_fibre_card_le_exact_shell_joint_min
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤
      min (targetDoubleShellTwoBitBridgeCarriers C exponent d).card
        (min (targetLowerExactShellColourSlots C exponent d).card
          (targetUpperExactShellColourSlots C exponent d).card) := by
  have hb := net_collision_fixed_diagonal_fibre_card_le_target_double_shell
    C exponent hexp honeLoss d
  have hl := net_collision_target_fibre_card_le_lower_exact_shell_slots
    C exponent hexp honeLoss d
  have hu := net_collision_target_fibre_card_le_upper_exact_shell_slots
    C exponent hexp honeLoss d
  exact Nat.le_min.mpr ⟨hb, Nat.le_min.mpr ⟨hl, hu⟩⟩

/-- The exact-shell joint bound refines the previous coarse joint
bridge/endpoint-colour capacity for every target, irrespective of
whether that target lies in the literal TRUE-hole complement. -/
theorem net_collision_exact_shell_joint_capacity_le_coarse_joint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool) :
    min (targetDoubleShellTwoBitBridgeCarriers C exponent d).card
      (min (targetLowerExactShellColourSlots C exponent d).card
        (targetUpperExactShellColourSlots C exponent d).card) ≤
    min (targetDoubleShellTwoBitBridgeCarriers C exponent d).card
      (min (targetLowerDoubleShellInactiveColourSlots C exponent d).card
        (targetUpperDoubleShellInactiveColourSlots C exponent d).card) := by
  have hl : (targetLowerExactShellColourSlots C exponent d).card ≤
      (targetLowerDoubleShellInactiveColourSlots C exponent d).card :=
    Finset.card_le_card
      (target_lower_exact_shell_slots_subset_coarse C exponent d)
  have hu : (targetUpperExactShellColourSlots C exponent d).card ≤
      (targetUpperDoubleShellInactiveColourSlots C exponent d).card :=
    Finset.card_le_card
      (target_upper_exact_shell_slots_subset_coarse C exponent d)
  omega

/-- Full actual NET canonical duplicate debt, with no injected
hole credit, is bounded by the sum of TARGET-EXACT bridge/colour
joint-capacity EXCESSES. -/
theorem net_collision_duplicate_debt_le_sum_exact_shell_joint_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        (min (targetDoubleShellTwoBitBridgeCarriers C exponent d).card
          (min (targetLowerExactShellColourSlots C exponent d).card
            (targetUpperExactShellColourSlots C exponent d).card) - 1) := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_le_sum
  intro d hd
  have hcap := net_collision_diagonal_fibre_card_le_exact_shell_joint_min
    C exponent hexp honeLoss d
  omega

/-- Sufficient condition for no actual canonical duplicate image
is target-by-target exact-shell joint capacity <=1. No theorem
currently derives this from ALL real planar AngleCap configurations. -/
theorem net_collision_duplicate_debt_zero_of_exact_shell_joint_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hunique : ∀ d ∈ netCollisionCertifiedDiagonalWords
      C exponent hexp honeLoss,
      min (targetDoubleShellTwoBitBridgeCarriers C exponent d).card
        (min (targetLowerExactShellColourSlots C exponent d).card
          (targetUpperExactShellColourSlots C exponent d).card) ≤ 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss = 0 := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_eq_zero
  intro d hd
  have hcap := net_collision_diagonal_fibre_card_le_exact_shell_joint_min
    C exponent hexp honeLoss d
  have hone := hunique d hd
  omega

/-- Actual NET mobile forward/reverse hard masses are bounded by
literal global Boolean holes, singleton/soft covered words, DISTINCT
already covered diagonals, and the target-EXACT joint slot EXCESS.
No covered target is treated as a hole, and unused covered sink
credit remains unclaimed rather than double-counted. -/
theorem net_mobile_mass_le_holes_covered_exact_shell_joint_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
      (softOverlapCompletionWords C).card +
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card +
      (netCollisionCertifiedCoveredDiagonals C exponent hexp honeLoss).card +
      (∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        (min (targetDoubleShellTwoBitBridgeCarriers C exponent d).card
          (min (targetLowerExactShellColourSlots C exponent d).card
            (targetUpperExactShellColourSlots C exponent d).card) - 1)) := by
  have hmobile := net_mobile_mass_le_singleton_soft_holes_blockers_duplicates
    C exponent hexp honeLoss
  have hdup := net_collision_duplicate_debt_le_sum_exact_shell_joint_excess
    C exponent hexp honeLoss
  omega

#print axioms net_collision_diagonal_fibre_card_le_exact_shell_joint_min
#print axioms net_collision_exact_shell_joint_capacity_le_coarse_joint
#print axioms net_collision_duplicate_debt_le_sum_exact_shell_joint_excess
#print axioms net_collision_duplicate_debt_zero_of_exact_shell_joint_unique
#print axioms net_mobile_mass_le_holes_covered_exact_shell_joint_excess

end OrderedEdgeColoring
end JSP000404Research
