import JSP000404Research.ResidualNetCollisionOriginalBridgeMatchingDominance
import JSP000404Research.ResidualNetCollisionTwinMatchingJointPayment
import Mathlib.Tactic

/-!
# Source-native original-vertex bridge matching with TWIN reservation

Two unrelated constraints on each ACTUAL NET diagonal fibre can be combined:
(1) the true original-centre-disjoint SOFT bridge matching number mu(d)
    (not merely a coloured endpoint-slot matching),
(2) the original hard-pair VERTEX budget after explicitly reserving all
    terminal equal-exponent TWIN rigid hard carriers.

    |F_d| <= min(mu(d), floor((|V| - 2*|T|)/4)).

The combined upper bound is <= BOTH previously certified estimates:
source-native original bridge matching + unreserved |V|/4,
and slot-matching + TWIN-reserved |V|/4.

This tightens an ACTUAL collision duplicate upper bound and the mobile
hard-source ledger, while retaining distinction between TRUE Boolean
holes and covered NET diagonals. It is NOT an allocation of these
resources to global six-source AngleCap geometric payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem net_collision_fibre_original_matching_twin_reserved_min
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤
      min (targetExactShellOriginalVertexMatchingNumber C exponent d)
        ((Fintype.card V -
           2 * (netTwinRigidCarriers C exponent).card) / 4) := by
  exact le_min
    (net_collision_fibre_card_le_original_vertex_matching_number
      C exponent hexp honeLoss d)
    (net_collision_fibre_card_le_twin_adjusted_quarter
      C exponent hexp honeLoss d)

/-- The new original-vertex matching cap is no larger than the
coloured slot matching cap with precisely the SAME TWIN reservation. -/
theorem net_collision_original_twin_min_le_slot_twin_min
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (d : Fin n → Bool) :
    min (targetExactShellOriginalVertexMatchingNumber C exponent d)
        ((Fintype.card V -
           2 * (netTwinRigidCarriers C exponent).card) / 4) ≤
      min (targetExactShellSlotMatchingNumber C exponent d)
        ((Fintype.card V -
           2 * (netTwinRigidCarriers C exponent).card) / 4) := by
  exact min_le_min_right _
    (target_exact_shell_original_vertex_number_le_slot_number
      C exponent d)

/-- Reserving TWIN carriers can only decrease, never increase, the
original-centre matching / vertex-quarter joint upper bound. -/
theorem net_collision_original_twin_min_le_original_quarter_min
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (d : Fin n → Bool) :
    min (targetExactShellOriginalVertexMatchingNumber C exponent d)
        ((Fintype.card V -
           2 * (netTwinRigidCarriers C exponent).card) / 4) ≤
      min (targetExactShellOriginalVertexMatchingNumber C exponent d)
        (Fintype.card V / 4) := by
  apply min_le_min_left
  omega

/-- Precise per-distinct-target NET duplicate-image excess upper bound.
The SAME original-centre matching budget is NOT summed globally:
only separately valid fibre EXCESS bounds are summed here. -/
theorem net_collision_duplicate_debt_le_original_twin_matching_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        (min (targetExactShellOriginalVertexMatchingNumber C exponent d)
          ((Fintype.card V -
            2 * (netTwinRigidCarriers C exponent).card) / 4) - 1) := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_le_sum
  intro d hd
  have hbound := net_collision_fibre_original_matching_twin_reserved_min
    C exponent hexp honeLoss d
  omega

/-- Actual mobile hard words bound, preserving all covered-diagonal
blockers separately from TRUE Boolean holes and now charging original
source BRIDGE matching capacity with terminal TWIN vertex reservation. -/
theorem net_mobile_mass_le_holes_covered_original_twin_matching_excess
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
      (netCollisionCertifiedCoveredDiagonals
        C exponent hexp honeLoss).card +
      (∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        (min (targetExactShellOriginalVertexMatchingNumber C exponent d)
          ((Fintype.card V -
            2 * (netTwinRigidCarriers C exponent).card) / 4) - 1)) := by
  have hm := net_mobile_mass_le_singleton_soft_holes_blockers_duplicates
    C exponent hexp honeLoss
  have hd := net_collision_duplicate_debt_le_original_twin_matching_excess
    C exponent hexp honeLoss
  omega

#print axioms net_collision_fibre_original_matching_twin_reserved_min
#print axioms net_collision_original_twin_min_le_slot_twin_min
#print axioms net_collision_original_twin_min_le_original_quarter_min
#print axioms net_collision_duplicate_debt_le_original_twin_matching_excess
#print axioms net_mobile_mass_le_holes_covered_original_twin_matching_excess

end OrderedEdgeColoring
end JSP000404Research
