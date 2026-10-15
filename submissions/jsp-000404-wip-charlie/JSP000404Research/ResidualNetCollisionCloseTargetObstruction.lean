import JSP000404Research.ResidualNetCollisionParitySeparatedRefund
import Mathlib.Tactic

/-!
# Unconditional CLOSE-PAIR obstruction to nonreused NET first-hit payment

The failure of "one actual SOFT shadow word pays at most once" is not
abstract: it forces TWO DIFFERENT ACTUAL attained NET diagonal targets
that differ in exactly TWO or exactly FOUR Boolean coordinates.

This is a direct, sorry-free obstruction witness. It removes the strong
pairwise separation premise from the CONCLUSION by making the local
target-pair obstruction explicit as the alternative to full SOFT first-
hit payment. It does NOT assert either that the obstruction is excluded
by planar AngleCap or that SOFT coverage constitutes true-hole credit.
The full six-source planar payment still has its admitted sorry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A strict violation of the distinct-SOFT first-hit payment forces a
pair of ACTUALLY ATTAINED NET targets separated by exactly 2 or 4 bits. -/
theorem net_soft_first_hit_failure_forces_two_or_four_target_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hfail :
      (softOverlapCompletionWords C).card <
        netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
        (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card) :
    ∃ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
      ∃ e ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        d ≠ e ∧
          ((Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card = 2 ∨
           (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card = 4) := by
  classical
  by_contra hnone
  have hsep :
      ∀ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
      ∀ e ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        d ≠ e →
          (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card ≠ 2 ∧
          (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card ≠ 4 := by
    intro d hd e he hde
    constructor
    · intro h2
      exact hnone ⟨d, hd, e, he, hde, Or.inl h2⟩
    · intro h4
      exact hnone ⟨d, hd, e, he, hde, Or.inr h4⟩
  have hbudget :=
    net_first_hits_plus_duplicates_le_soft_of_no_two_four_target_pairs
      C exponent hexp honeLoss hsep
  omega

/-- Unconditionally: either actual NET first-hit debt admits a
distinct-SOFT-cardinality budget, or an actual pair of attained
diagonals differs by exactly two or four coordinates. -/
theorem net_first_hits_paid_or_actual_close_target_obstruction
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
      (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card ≤
        (softOverlapCompletionWords C).card) ∨
    (∃ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
      ∃ e ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        d ≠ e ∧
          ((Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card = 2 ∨
           (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card = 4)) := by
  classical
  by_cases hpaid :
      netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
        (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card ≤
          (softOverlapCompletionWords C).card
  · exact Or.inl hpaid
  · right
    have hfail :
      (softOverlapCompletionWords C).card <
        netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
          (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card := by
      omega
    exact net_soft_first_hit_failure_forces_two_or_four_target_pair
      C exponent hexp honeLoss hfail

#print axioms net_soft_first_hit_failure_forces_two_or_four_target_pair
#print axioms net_first_hits_paid_or_actual_close_target_obstruction

end OrderedEdgeColoring
end JSP000404Research
