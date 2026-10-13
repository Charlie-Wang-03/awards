import JSP000404Research.ResidualNetCollisionCertifiedGlobalLedger
import Mathlib.Tactic

/-!
# Exact mobile-source accounting with ACTUAL canonical hole diagonals

Compose the two independent certified identities:
(1) unpaid forward hard + reverse strict-rigid + unused covered sinks
      = singleton + soft + genuine NET cross-map sink collisions;
(2) genuine NET collisions
      = distinct TRUE-hole canonical diagonals
        + distinct COVERED canonical diagonals
        + duplicate canonical diagonal hits.

This eliminates the opaque actual-collision cardinal from the global
mobile-source conservation law. No candidate bridge overcount,
duplicate hole payment, or hidden global injectivity is used.

Still open: how to pay for the covered diagonals and duplicate hits
from REAL unreserved profile surplus / other geometric resources;
how to pay the terminal twin, mixed-rigid, soft, and projected-loss
debts. This identity does not discharge the sole WIP sorry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Exact accounting for BOTH genuinely unpaid mobile hard-source
families, now resolved through the canonical actual diagonal
image into REAL holes, actual external-covered blockers, and
unpaid multiple-hit debt. -/
theorem net_mobile_source_plus_unused_eq_certified_three_diagonals
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card +
      (netMobileUnusedCoveredSinkWords
        C exponent hexp honeLoss).card =
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card +
        (netCollisionCertifiedTrueHoleDiagonals
          C exponent hexp honeLoss).card +
        (netCollisionCertifiedCoveredDiagonals
          C exponent hexp honeLoss).card +
        netCollisionCertifiedDuplicateDebt
          C exponent hexp honeLoss := by
  have hmobile :=
    net_mobile_source_plus_unused_eq_covered_plus_actual
      C exponent hexp honeLoss
  have hdiag :=
    net_collision_certified_diagonal_exact_three_debts
      C exponent hexp honeLoss
  omega

/-- For ANY remaining debt and any genuine available budget,
the NET mobile payment obligation can be rewritten into a
certified global true-hole payment plus TWO concrete residual
obstructions: source/fifth-centre covered diagonals and actual
duplicate images. Unused singleton/soft sinks stay explicitly
on the capacity side; covered sinks are not renamed as holes. -/
theorem net_mobile_payment_iff_certified_true_hole_blocker_duplicate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (otherDebt availableBudget : ℕ) :
    (otherDebt +
      (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤
      availableBudget) ↔
    (otherDebt +
        (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card +
        (netCollisionCertifiedTrueHoleDiagonals
          C exponent hexp honeLoss).card +
        (netCollisionCertifiedCoveredDiagonals
          C exponent hexp honeLoss).card +
        netCollisionCertifiedDuplicateDebt
          C exponent hexp honeLoss ≤
      availableBudget +
        (netMobileUnusedCoveredSinkWords
          C exponent hexp honeLoss).card) := by
  have hnet :=
    net_mobile_source_plus_unused_eq_certified_three_diagonals
      C exponent hexp honeLoss
  omega

/-- The same global MOBILE source inequality may be expressed
using the total number of TRUE Boolean holes (instead of just
the chosen canonical diagonal holes), but the exact covered
and duplicate obstructions must be kept. -/
theorem net_mobile_mass_le_singleton_soft_holes_blockers_duplicates
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
      netCollisionCertifiedDuplicateDebt
        C exponent hexp honeLoss := by
  have hsource :=
    net_mobile_source_plus_unused_eq_certified_three_diagonals
      C exponent hexp honeLoss
  have hholes :
      (netCollisionCertifiedTrueHoleDiagonals
        C exponent hexp honeLoss).card ≤
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card := by
    exact Finset.card_le_card (Finset.inter_subset_right)
  omega

#print axioms net_mobile_source_plus_unused_eq_certified_three_diagonals
#print axioms net_mobile_payment_iff_certified_true_hole_blocker_duplicate
#print axioms net_mobile_mass_le_singleton_soft_holes_blockers_duplicates

end OrderedEdgeColoring
end JSP000404Research
