import JSP000404Research.ResidualNetCollisionShadowFirstUseReuseDefect
import JSP000404Research.ResidualNetCollisionTrueHoleRefundShadowLedger
import Mathlib.Tactic

/-!
# True NET-hole refund with a separately itemized SOFT reuse defect

Two independently justified ledgers are now combined:
1. Actual NET-hit TRUE Boolean holes are EXCLUDED from the free-hole
   budget, and already-covered target blockers cancel.
2. The ACTUAL SOFT target-shadow incidence count is split EXACTLY into
   unique first uses and additional cross-target reuses.

The final RHS still carries the complete reuse deficit explicitly.
No assertion identifies a covered SOFT word with a true Boolean hole
or with otherwise unreserved dyadic payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Actual NET mobile sources after TRUE-hole first-hit refunds,
with SOFT shadows billed once for their first use and an ADDITIONAL
explicit integer deficit for every repeated target incidence. -/
theorem net_mobile_mass_le_unhit_true_holes_first_soft_uses_plus_reuse
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
    let S := softOverlapCompletionWords C
    let deg : (Fin n → Bool) → ℕ := fun s =>
      (D.filter (fun d =>
        (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card
    (netTransportableHardWords C exponent).card +
        (netStrictDescentRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card +
        (((Finset.univ : Finset (Fin n → Bool)) \
          coveredCompletionWords C).card -
          (netCollisionCertifiedTrueHoleDiagonals
            C exponent hexp honeLoss).card) +
        (S.filter (fun s => 0 < deg s)).card +
        (∑ s ∈ S, (deg s - 1)) := by
  classical
  dsimp
  let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
  let S := softOverlapCompletionWords C
  let deg : (Fin n → Bool) → ℕ := fun s =>
      (D.filter (fun d =>
        (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card
  have hmobile := net_mobile_mass_le_unhit_true_holes_plus_global_soft_incidence
    C exponent hexp honeLoss
  have hsplit := finite_degree_first_use_plus_reuse_exact S deg
  change (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤
    (singletonCompletionWords C).card +
      (softOverlapCompletionWords C).card +
      (((Finset.univ : Finset (Fin n → Bool)) \
          coveredCompletionWords C).card -
          (netCollisionCertifiedTrueHoleDiagonals
            C exponent hexp honeLoss).card) +
      (∑ s ∈ S, deg s) at hmobile
  calc
    (netTransportableHardWords C exponent).card +
        (netStrictDescentRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card +
        (((Finset.univ : Finset (Fin n → Bool)) \
            coveredCompletionWords C).card -
            (netCollisionCertifiedTrueHoleDiagonals
              C exponent hexp honeLoss).card) +
        (∑ s ∈ S, deg s) := hmobile
    _ = (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card +
        (((Finset.univ : Finset (Fin n → Bool)) \
            coveredCompletionWords C).card -
            (netCollisionCertifiedTrueHoleDiagonals
              C exponent hexp honeLoss).card) +
        (S.filter (fun s => 0 < deg s)).card +
        (∑ s ∈ S, (deg s - 1)) := by
          rw [hsplit]
          omega

#print axioms net_mobile_mass_le_unhit_true_holes_first_soft_uses_plus_reuse

end OrderedEdgeColoring
end JSP000404Research
