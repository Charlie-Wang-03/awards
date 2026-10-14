import JSP000404Research.ResidualNetCollisionTwinAdjustedFibre
import JSP000404Research.ResidualNetCollisionVertexBudgetFibre
import Mathlib.Tactic

/-!
# Exact NET target matching capacity with terminal TWIN hard ownership

For every REAL collision diagonal target d, two independently proved
restrictions on the same source fibre must hold simultaneously:

* candidate exact-shell source slot matching number nu(G_d),
* original HARD carrier matching after reserving ALL terminal TWIN
  rigid pairs: floor((|V|-2|T|)/4).

Hence |F_d| <= min(nu(G_d), floor((|V|-2|T|)/4)).
Summation over DISTINCT ACTUAL targets bounds the exact duplicate debt.
The covered-target vs TRUE hole distinction is retained in the
resulting mobile-source ledger.

This is a sharper COMBINATORIAL CAPACITY, not a hole, surplus or
global six-source payment certificate.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem net_collision_fibre_card_le_matching_twin_adjusted_min
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤
      min (targetExactShellSlotMatchingNumber C exponent d)
        ((Fintype.card V -
            2 * (netTwinRigidCarriers C exponent).card) / 4) := by
  exact le_min
    (net_collision_target_fibre_card_le_matching_number
      C exponent hexp honeLoss d)
    (net_collision_fibre_card_le_twin_adjusted_quarter
      C exponent hexp honeLoss d)

/-- The TWIN-adjusted matching cap cannot exceed the previous cap
that ignored the vertices occupied by terminal TWIN hard carriers. -/
theorem net_collision_twin_adjusted_min_le_original_matching_vertex_min
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (d : Fin n → Bool) :
    min (targetExactShellSlotMatchingNumber C exponent d)
      ((Fintype.card V -
          2 * (netTwinRigidCarriers C exponent).card) / 4) ≤
    min (targetExactShellSlotMatchingNumber C exponent d)
      (Fintype.card V / 4) := by
  apply min_le_min_left
  omega

/-- Exact duplicate-image debt with TWIN-reserved vertex slots and
target-exact candidate matching capacity, each target charged ONCE. -/
theorem net_collision_duplicate_debt_le_matching_twin_adjusted_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        (min (targetExactShellSlotMatchingNumber C exponent d)
          ((Fintype.card V -
            2 * (netTwinRigidCarriers C exponent).card) / 4) - 1) := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_le_sum
  intro d hd
  have hbound := net_collision_fibre_card_le_matching_twin_adjusted_min
    C exponent hexp honeLoss d
  omega

/-- Mobile hard source bound retaining literal true Boolean holes
and the distinct already-COVERED target blocker account, while
charging no more than joint source matching and TWIN-adjusted
original vertex capacity. -/
theorem net_mobile_mass_le_holes_covered_matching_twin_adjusted_excess
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
        (min (targetExactShellSlotMatchingNumber C exponent d)
          ((Fintype.card V -
            2 * (netTwinRigidCarriers C exponent).card) / 4) - 1)) := by
  have hm := net_mobile_mass_le_singleton_soft_holes_blockers_duplicates
    C exponent hexp honeLoss
  have hd := net_collision_duplicate_debt_le_matching_twin_adjusted_excess
    C exponent hexp honeLoss
  omega

#print axioms net_collision_fibre_card_le_matching_twin_adjusted_min
#print axioms net_collision_twin_adjusted_min_le_original_matching_vertex_min
#print axioms net_collision_duplicate_debt_le_matching_twin_adjusted_excess
#print axioms net_mobile_mass_le_holes_covered_matching_twin_adjusted_excess

end OrderedEdgeColoring
end JSP000404Research
