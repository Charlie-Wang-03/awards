import JSP000404Research.ResidualNetCollisionExactShellBipartiteCover
import Mathlib.Tactic

/-!
# Target-exact disjoint-slot matching obstruction

Two distinct real NET sources hitting the SAME canonical diagonal cannot
share an original lower/reverse-colour slot, and cannot share an original
upper/forward-colour slot. Hence two sources certify TWO vertex-disjoint
edges in the genuine target-exact candidate slot graph.

Conversely, if the candidate graph has no two slot-disjoint edges, an
actual target fibre has at most one source. If this holds for every
actually hit diagonal, genuine duplicate-image debt is ZERO.

Unlike a global "one candidate bridge" or "one candidate slot" hypothesis,
the matching-free graph hypothesis permits arbitrarily many candidate
edges sharing a common endpoint (stars). It is a still-unproved
GEOMETRIC hypothesis, not a theorem under arbitrary planar AngleCap.
No covered diagonal or slot becomes a TRUE Boolean hole.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Pairwise edge incidence in the target-exact candidate graph
forbids two ACTUAL NET sources with that canonical target. -/
theorem net_collision_target_fibre_card_le_one_of_no_disjoint_slot_edges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool)
    (hintersect : ∀ e ∈ targetExactShellSlotEdges C exponent d,
      ∀ f ∈ targetExactShellSlotEdges C exponent d,
        e.1 = f.1 ∨ e.2 = f.2) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro s hs t ht
  have hds :
      netCollisionCertifiedDiagonal C exponent hexp honeLoss s = d :=
    (Finset.mem_filter.mp hs).2
  have hdt :
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t = d :=
    (Finset.mem_filter.mp ht).2
  have hse := net_collision_actual_pair_mem_exact_shell_slot_edges
    C exponent hexp honeLoss s
  have hte := net_collision_actual_pair_mem_exact_shell_slot_edges
    C exponent hexp honeLoss t
  rw [hds] at hse
  rw [hdt] at hte
  rcases hintersect
      (netCollisionCertifiedLowerColourSlot C exponent hexp honeLoss s,
       netCollisionCertifiedUpperColourSlot C exponent hexp honeLoss s) hse
      (netCollisionCertifiedLowerColourSlot C exponent hexp honeLoss t,
       netCollisionCertifiedUpperColourSlot C exponent hexp honeLoss t) hte
    with hl | hu
  · exact net_collision_same_target_lower_slot_injective
      C exponent hexp honeLoss s t (hds.trans hdt.symm) hl
  · exact net_collision_same_target_upper_slot_injective
      C exponent hexp honeLoss s t (hds.trans hdt.symm) hu

/-- If a target fibre has two or more actual sources, TWO allowed
candidate edges are disjoint in BOTH labelled slot endpoints.
This is the precise necessary combinatorial obstruction remaining
before any target-specific planar geometric matching exclusion. -/
theorem net_collision_two_disjoint_slot_edges_of_fibre_card_gt_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool)
    (hmulti : 1 <
      (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card) :
    ∃ e ∈ targetExactShellSlotEdges C exponent d,
      ∃ f ∈ targetExactShellSlotEdges C exponent d,
        e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by
  classical
  by_contra hnone
  have hintersect : ∀ e ∈ targetExactShellSlotEdges C exponent d,
      ∀ f ∈ targetExactShellSlotEdges C exponent d,
        e.1 = f.1 ∨ e.2 = f.2 := by
    intro e he f hf
    by_cases hl : e.1 = f.1
    · exact Or.inl hl
    · right
      by_contra hu
      exact hnone ⟨e, he, f, hf, hl, hu⟩
  have hle := net_collision_target_fibre_card_le_one_of_no_disjoint_slot_edges
    C exponent hexp honeLoss d hintersect
  omega

/-- A matching-free exact-shell candidate graph at EVERY actually
hit diagonal removes ALL genuine NET multiple-hit debt.
The hypothesis remains a substantive, unproved planar obligation. -/
theorem net_collision_duplicate_debt_zero_of_no_disjoint_slot_edges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hintersect : ∀ d ∈ netCollisionCertifiedDiagonalWords
      C exponent hexp honeLoss,
      ∀ e ∈ targetExactShellSlotEdges C exponent d,
      ∀ f ∈ targetExactShellSlotEdges C exponent d,
        e.1 = f.1 ∨ e.2 = f.2) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss = 0 := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_eq_zero
  intro d hd
  have hle := net_collision_target_fibre_card_le_one_of_no_disjoint_slot_edges
    C exponent hexp honeLoss d (hintersect d hd)
  omega

/-- Under the explicitly matching-free candidate-graph condition,
the ACTUAL unpaid mobile source ledger no longer has duplicate debt.
All remaining quantities are still literal and disjointly classified:
TRUE holes, already covered diagonals, and singleton/soft covered words.
This is not the open six-source global payment theorem. -/
theorem net_mobile_mass_le_holes_covered_of_no_disjoint_slot_edges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hintersect : ∀ d ∈ netCollisionCertifiedDiagonalWords
      C exponent hexp honeLoss,
      ∀ e ∈ targetExactShellSlotEdges C exponent d,
      ∀ f ∈ targetExactShellSlotEdges C exponent d,
        e.1 = f.1 ∨ e.2 = f.2) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
      (softOverlapCompletionWords C).card +
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card +
      (netCollisionCertifiedCoveredDiagonals
        C exponent hexp honeLoss).card := by
  have hzero := net_collision_duplicate_debt_zero_of_no_disjoint_slot_edges
    C exponent hexp honeLoss hintersect
  have hledger := net_mobile_mass_le_singleton_soft_holes_blockers_duplicates
    C exponent hexp honeLoss
  omega

#print axioms net_collision_target_fibre_card_le_one_of_no_disjoint_slot_edges
#print axioms net_collision_two_disjoint_slot_edges_of_fibre_card_gt_one
#print axioms net_collision_duplicate_debt_zero_of_no_disjoint_slot_edges
#print axioms net_mobile_mass_le_holes_covered_of_no_disjoint_slot_edges

end OrderedEdgeColoring
end JSP000404Research
