import JSP000404Research.ResidualNetCollisionShadowFirstHitGlobalCharge
import JSP000404Research.ResidualTwoShadowTargetSeparation
import Mathlib.Tactic

/-!
# A geometric target-separation gate for nonreused NET/SOFT first-hit payment

The actual NET source first-hit plus duplicate budget is bounded by the
global SOFT-to-diagonal Hamming-two incidence count. When distinct ACTUAL
diagonal targets are separated by more than four Boolean coordinates,
our standalone four-bit support theorem proves that each SOFT word has
at most one such target. The resulting charge pays each SOFT word once.

This is a new CONDITIONAL bridge reducing the nonreuse question to a
precise target-separation property. It does not assert that planar
AngleCap enforces the separation, or that SOFT covered words are true
holes or unreserved dyadic surplus. The full six-source sorry is open.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Under pairwise Hamming separation greater than four between
distinct attained NET diagonal targets, the first-hit image plus
duplicate source excess fits into the distinct SOFT shadow inventory.
No planar separation is assumed without proof. -/
theorem net_first_hits_plus_duplicates_le_soft_of_target_five_separation
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hsep :
      ∀ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
      ∀ e ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        d ≠ e →
          4 < (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
      (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card ≤
        (softOverlapCompletionWords C).card := by
  classical
  let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
  let S := softOverlapCompletionWords C
  let deg : (Fin n → Bool) → ℕ := fun s =>
    (D.filter (fun d =>
      (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card
  have hbase :=
    net_duplicate_plus_distinct_hits_le_soft_shadow_incidence
      C exponent hexp honeLoss
  change netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
    D.card ≤ ∑ s ∈ S, deg s at hbase
  have hone : ∀ s ∈ S, deg s ≤ 1 := by
    intro s hs
    exact five_separated_targets_two_shadow_degree_le_one D hsep s
  calc
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
        D.card ≤ ∑ s ∈ S, deg s := hbase
    _ ≤ ∑ _s ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro s hs
      exact hone s hs
    _ = S.card := by simp

#print axioms net_first_hits_plus_duplicates_le_soft_of_target_five_separation

end OrderedEdgeColoring
end JSP000404Research
