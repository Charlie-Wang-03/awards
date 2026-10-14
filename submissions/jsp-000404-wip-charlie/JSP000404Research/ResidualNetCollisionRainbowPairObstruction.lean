import JSP000404Research.ResidualNetCollisionRainbowMatchingCapacity
import Mathlib.Tactic

/-!
# Conditional two-edge obstruction for true NET duplicate debt

The conditional "all slot-disjoint candidate edge pairs have equal
unordered colour supports" suffices to eliminate NET duplicate debt;
this remains a fully verified correct theorem. Positive actual debt
forces two slot-disjoint edges with different support.

IMPORTANT LATER CORRECTION: such a colour-equal candidate edge pair
is IMPOSSIBLE under the actual exact-shell graph definition, even
without knowing whether the edges are real NET sources. It follows
from the previously verified injective candidate shadow word map.
Thus the conditional two-edge hypothesis is EQUIVALENT to excluding
all distinct two-edge ordinary matchings, not a strictly weaker
geometric exclusion as previously claimed. See
ResidualNetCollisionRainbowRedundancyAudit.lean.

The AngleCap matching-exclusion and global six-source payment remain
open; the proved conditional implications are retained.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A rainbow matching has at most one edge whenever ANY two
disjoint-slot candidate edges must reuse the same unordered colour
support. In THIS graph no two distinct edges can share that support,
so the premise forbids every genuine two-edge ordinary matching. -/
theorem exact_shell_rainbow_matching_card_le_one_of_disjoint_colour_clash
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (hclash : ∀ e ∈ targetExactShellSlotEdges C exponent d,
      ∀ f ∈ targetExactShellSlotEdges C exponent d,
      e.1 ≠ f.1 → e.2 ≠ f.2 →
      targetExactShellEdgeColourSupport e =
        targetExactShellEdgeColourSupport f)
    (M : Finset ((V × Fin n) × (V × Fin n)))
    (hM : targetExactShellRainbowMatching C exponent d M) :
    M.card ≤ 1 := by
  classical
  obtain ⟨hsub, hl, hr, hcolour⟩ := hM
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra hne
  have hle : e.1 ≠ f.1 := by
    intro heq
    exact hne (hl e he f hf heq)
  have hre : e.2 ≠ f.2 := by
    intro heq
    exact hne (hr e he f hf heq)
  exact hne (hcolour e he f hf
    (hclash e (hsub he) f (hsub hf) hle hre))

/-- The exact rainbow matching number is at most one even when
a priori there could be ordinary two-edge matchings; but for this
particular graph a later audit rules out colour-reused edge pairs.
Formally the bound holds provided disjoint
candidate edges necessarily share their unordered flip colours. -/
theorem exact_shell_rainbow_matching_number_le_one_of_disjoint_colour_clash
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (hclash : ∀ e ∈ targetExactShellSlotEdges C exponent d,
      ∀ f ∈ targetExactShellSlotEdges C exponent d,
      e.1 ≠ f.1 → e.2 ≠ f.2 →
      targetExactShellEdgeColourSupport e =
        targetExactShellEdgeColourSupport f) :
    targetExactShellRainbowMatchingNumber C exponent d ≤ 1 := by
  classical
  unfold targetExactShellRainbowMatchingNumber
  apply Finset.sup_le
  intro M hM
  have hmem := (Finset.mem_filter.mp hM).2
  exact exact_shell_rainbow_matching_card_le_one_of_disjoint_colour_clash
    C exponent d hclash M hmem

/-- If the exact two-edge RAINBOW obstruction is absent at every
genuinely hit target, actual canonical duplicate debt VANISHES.
This is weaker than excluding all two-edge slot matchings. -/
theorem net_collision_duplicate_debt_zero_of_disjoint_colour_clash
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hclash : ∀ d ∈ netCollisionCertifiedDiagonalWords
      C exponent hexp honeLoss,
      ∀ e ∈ targetExactShellSlotEdges C exponent d,
      ∀ f ∈ targetExactShellSlotEdges C exponent d,
      e.1 ≠ f.1 → e.2 ≠ f.2 →
      targetExactShellEdgeColourSupport e =
        targetExactShellEdgeColourSupport f) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss = 0 := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_eq_zero
  intro d hd
  have hbound :=
    net_collision_target_fibre_card_le_rainbow_matching_number
      C exponent hexp honeLoss d
  have hcap :=
    exact_shell_rainbow_matching_number_le_one_of_disjoint_colour_clash
      C exponent d (hclash d hd)
  omega

/-- The true mobile-source accounting then has no duplicate debt.
No claimed conversion of covered diagonal slots into true holes. -/
theorem net_mobile_mass_le_holes_covered_of_disjoint_colour_clash
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hclash : ∀ d ∈ netCollisionCertifiedDiagonalWords
      C exponent hexp honeLoss,
      ∀ e ∈ targetExactShellSlotEdges C exponent d,
      ∀ f ∈ targetExactShellSlotEdges C exponent d,
      e.1 ≠ f.1 → e.2 ≠ f.2 →
      targetExactShellEdgeColourSupport e =
        targetExactShellEdgeColourSupport f) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
      (softOverlapCompletionWords C).card +
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card +
      (netCollisionCertifiedCoveredDiagonals
        C exponent hexp honeLoss).card := by
  have hmobile :=
    net_mobile_mass_le_singleton_soft_holes_blockers_duplicates
      C exponent hexp honeLoss
  have hzero :=
    net_collision_duplicate_debt_zero_of_disjoint_colour_clash
      C exponent hexp honeLoss hclash
  rw [hzero] at hmobile
  omega

/-- An honest source-native witness. Positive TRUE duplicate debt
forces two graph edges eligible for the SAME ACTUALLY HIT diagonal,
with no lower/upper slot collision AND no repeated unordered pair
of flip colours. This is a sharper geometric target than ordinary
two-edge matching nonexistence. -/
theorem net_collision_positive_duplicate_forces_two_rainbow_edges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hpos : 0 < netCollisionCertifiedDuplicateDebt
      C exponent hexp honeLoss) :
    ∃ d ∈ netCollisionCertifiedDiagonalWords
        C exponent hexp honeLoss,
      ∃ e ∈ targetExactShellSlotEdges C exponent d,
        ∃ f ∈ targetExactShellSlotEdges C exponent d,
          e.1 ≠ f.1 ∧ e.2 ≠ f.2 ∧
          targetExactShellEdgeColourSupport e ≠
            targetExactShellEdgeColourSupport f := by
  classical
  by_contra hnone
  have hclash : ∀ d ∈ netCollisionCertifiedDiagonalWords
      C exponent hexp honeLoss,
      ∀ e ∈ targetExactShellSlotEdges C exponent d,
      ∀ f ∈ targetExactShellSlotEdges C exponent d,
      e.1 ≠ f.1 → e.2 ≠ f.2 →
      targetExactShellEdgeColourSupport e =
        targetExactShellEdgeColourSupport f := by
    intro d hd e he f hf hle hre
    by_contra hdiff
    exact hnone ⟨d, hd, e, he, f, hf, hle, hre, hdiff⟩
  have hzero :=
    net_collision_duplicate_debt_zero_of_disjoint_colour_clash
      C exponent hexp honeLoss hclash
  omega

#print axioms exact_shell_rainbow_matching_card_le_one_of_disjoint_colour_clash
#print axioms exact_shell_rainbow_matching_number_le_one_of_disjoint_colour_clash
#print axioms net_collision_duplicate_debt_zero_of_disjoint_colour_clash
#print axioms net_mobile_mass_le_holes_covered_of_disjoint_colour_clash
#print axioms net_collision_positive_duplicate_forces_two_rainbow_edges

end OrderedEdgeColoring
end JSP000404Research
