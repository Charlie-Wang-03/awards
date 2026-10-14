import JSP000404Research.ResidualNetCollisionFullMatchingCertificate
import Mathlib.Tactic

/-!
# Unconditional exact-shell graph matching-number bound

For each canonical target d, define nu(d) as the maximum cardinality
of a matching in the FULL target-exact candidate edge graph.
This is a finite combinatorial invariant defined without an external
matching oracle or an unproved König theorem.

The actual NET source fibre itself yields such a matching, so its
size is at most nu(d). The source duplicate debt and mobile hard
source ledger inherit unconditional graph-structural upper bounds.

No theorem here bounds nu(d) by REAL Boolean holes, proves nu(d) small
from planar AngleCap, or pays the remaining five-plus debt classes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The graph-theoretic matching number of the exact-shell
candidate edge graph at target d. Its finite definition makes NO
implicit assumption about source realizability or geometric payment. -/
noncomputable def targetExactShellSlotMatchingNumber
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool) : ℕ := by
  classical
  exact
    ((Finset.univ : Finset (Finset ((V × Fin n) × (V × Fin n)))).filter
      (fun M =>
        M ⊆ targetExactShellSlotEdges C exponent d ∧
        (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) ∧
        (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f))).sup Finset.card

/-- Every certified matching has cardinal at most the target's
definitionally finite maximum-matching number. -/
theorem exact_shell_slot_matching_card_le_matching_number
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (M : Finset ((V × Fin n) × (V × Fin n)))
    (hsub : M ⊆ targetExactShellSlotEdges C exponent d)
    (hl : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hr : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) :
    M.card ≤ targetExactShellSlotMatchingNumber C exponent d := by
  classical
  unfold targetExactShellSlotMatchingNumber
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hsub, hl, hr⟩

/-- The genuine NET target fibre is bounded UNCONDITIONALLY by the
matching number of the target-specific genuine-source-compatible
candidate graph, which can be strictly below raw edge/slot counts. -/
theorem net_collision_target_fibre_card_le_matching_number
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤
      targetExactShellSlotMatchingNumber C exponent d := by
  exact net_collision_target_fibre_card_le_of_matching_certificate
    C exponent hexp honeLoss d
    (targetExactShellSlotMatchingNumber C exponent d)
    (fun M hsub hl hr =>
      exact_shell_slot_matching_card_le_matching_number
        C exponent d M hsub hl hr)

/-- An unconditional graph-theoretic upper bound on the genuine
NET canonical duplicate-image debt; no target is credited twice. -/
theorem net_collision_duplicate_debt_le_sum_matching_number_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        (targetExactShellSlotMatchingNumber C exponent d - 1) := by
  exact net_collision_duplicate_debt_le_matching_certificate_excess
    C exponent hexp honeLoss
    (targetExactShellSlotMatchingNumber C exponent)
    (by
      intro d _ M hsub hl hr
      exact exact_shell_slot_matching_card_le_matching_number
        C exponent d M hsub hl hr)

/-- Graph-optimal duplicate-source capacity substituted into the
literal-hole/covered-target mobile ledger. Candidate graph matching
slots are not misclassified as REAL Boolean holes or unreserved
profile surplus. This is NOT the six-source global payment. -/
theorem net_mobile_mass_le_holes_covered_matching_number_excess
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
        (targetExactShellSlotMatchingNumber C exponent d - 1)) := by
  have hmobile :=
    net_mobile_mass_le_singleton_soft_holes_blockers_duplicates
      C exponent hexp honeLoss
  have hmatching :=
    net_collision_duplicate_debt_le_sum_matching_number_excess
      C exponent hexp honeLoss
  omega

#print axioms exact_shell_slot_matching_card_le_matching_number
#print axioms net_collision_target_fibre_card_le_matching_number
#print axioms net_collision_duplicate_debt_le_sum_matching_number_excess
#print axioms net_mobile_mass_le_holes_covered_matching_number_excess

end OrderedEdgeColoring
end JSP000404Research
