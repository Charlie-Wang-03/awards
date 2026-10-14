import JSP000404Research.ResidualFiniteBipartiteCoverCapacity
import JSP000404Research.ResidualNetCollisionExactShellPaymentBound
import Mathlib.Tactic

/-!
# Genuine NET canonical collision fibres obey every geometric
# target-specific bipartite vertex-cover capacity

For each ACTUALLY hit canonical opposite diagonal d, make an
eligible bipartite graph. A possible edge joins a LOWER (b, cr)
endpoint/reverse-flip slot to an UPPER (v, cf)
endpoint/forward-flip slot only when:
  (b,v) is an actual-hard-source-COMPATIBLE double-shell SOFT bridge;
  cr is an exact retained active-bit VIOLATION of d at v;
  cf is an exact retained active-bit VIOLATION of d at b.

Each REAL NET collision of target d maps to a permitted graph edge,
and is individually injectively determined by EITHER endpoint slot,
using the already verified same-target original-colour rigidity.

Consequently, for ANY verified vertex cover (A,B) of this eligible
graph, |real source fibre at d| <= |A|+|B|, charging each actual
source ONCE to one side. Sparse graph incidence can give a bound
STRICTLY stronger than min(|eligible lower slots|,|eligible upper slots|).

No extra AngleCap assumption, no Boolean hole credit, no assumption
that every eligible SOFT edge is an actual NET collision.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Original source-certified lower vertex / reverse hard flip
colour attached to a genuine NET collision sink word. -/
noncomputable def netCollisionCertifiedLowerColourSlot
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}) :
    V × Fin n :=
  ((netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).1,
    strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)))

/-- Original source-certified upper vertex / forward hard flip colour. -/
noncomputable def netCollisionCertifiedUpperColourSlot
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}) :
    V × Fin n :=
  ((netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).2,
    transportablePairColor C
      (transportableWordCarrier C
        (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)))

/-- Only genuinely source-compatible double-shell candidate bridges
connecting mutually compatible exact opposite endpoint violations
are eligible as an edge. No false hole/payment assertion is built in. -/
noncomputable def targetExactShellSlotEdges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (d : Fin n → Bool) : Finset ((V × Fin n) × (V × Fin n)) := by
  classical
  exact Finset.univ.filter (fun e =>
    (e.1.1,e.2.1) ∈ targetDoubleShellTwoBitBridgeCarriers C exponent d ∧
    e.1.2 ∈ retainedActiveViolationCoords C e.2.1 d ∧
    e.2.2 ∈ retainedActiveViolationCoords C e.1.1 d ∧
    e.1.2 ∉ retainedActive C e.1.1 ∧
    e.2.2 ∉ retainedActive C e.2.1)

/-- ACTUAL canonical NET sources define actual EDGES in the
geometrically permitted target-dependent candidate-slot graph. -/
theorem net_collision_actual_pair_mem_exact_shell_slot_edges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}) :
    (netCollisionCertifiedLowerColourSlot C exponent hexp honeLoss s,
     netCollisionCertifiedUpperColourSlot C exponent hexp honeLoss s) ∈
    targetExactShellSlotEdges C exponent
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss s) := by
  classical
  let x := netCollisionCertifiedForwardSource C exponent hexp honeLoss s
  let y := netCollisionCertifiedReverseSource C exponent hexp honeLoss s
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let d := netCollisionCertifiedDiagonal C exponent hexp honeLoss s
  have hb := net_collision_bridge_owner_mem_target_double_shell
    C exponent hexp honeLoss s
  change (q.1.1, p.1.2) ∈
    targetDoubleShellTwoBitBridgeCarriers C exponent d at hb
  have hshell := net_collision_certified_diagonal_exact_two_endpoint_shells
    C exponent hexp honeLoss s
  change retainedActiveViolationCoords C q.1.1 d = {cf} ∧
    retainedActiveViolationCoords C p.1.2 d = {cr} at hshell
  change ((q.1.1,cr),(p.1.2,cf)) ∈ targetExactShellSlotEdges C exponent d
  have hnotcr : cr ∉ retainedActive C q.1.1 :=
    (strictDescentRigidPairColor_spec C exponent hexp honeLoss q).2
  have hnotcf : cf ∉ retainedActive C p.1.2 :=
    (transportablePairColor_spec C p).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hb, ?_, ?_, hnotcr, hnotcf⟩
  · rw [hshell.2]
    simp
  · rw [hshell.1]
    simp

/-- The tightened candidate edge graph no longer contains
original-colour slots active at their OWN endpoint. Thus BOTH
endpoints of EVERY candidate graph edge lie in the previously
certified target-EXACT lower and upper slot sets.
This is stronger than the prior graph definition which checked
only the opposite endpoint's violated colour. -/
theorem target_exact_shell_edge_endpoints_mem_exact_colour_slots
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (e : (V × Fin n) × (V × Fin n))
    (he : e ∈ targetExactShellSlotEdges C exponent d) :
    e.1 ∈ targetLowerExactShellColourSlots C exponent d ∧
    e.2 ∈ targetUpperExactShellColourSlots C exponent d := by
  classical
  obtain ⟨_, hb, hcr, hcf, hnotcr, hnotcf⟩ :=
    Finset.mem_filter.mp he
  constructor
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hnotcr, ⟨e.2.1, hb, hcr⟩⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hnotcf, ⟨e.1.1, hb, hcf⟩⟩

/-- A common canonical target and the same LOWER endpoint-colour slot
force the original NET collision word to be identical. -/
theorem net_collision_same_target_lower_slot_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss})
    (hdiag : netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t)
    (hslot : netCollisionCertifiedLowerColourSlot C exponent hexp honeLoss s =
      netCollisionCertifiedLowerColourSlot C exponent hexp honeLoss t) :
    s = t := by
  have hb := congrArg (fun z : V × Fin n => z.1) hslot
  have hcr := congrArg (fun z : V × Fin n => z.2) hslot
  change (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).1 =
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).1 at hb
  change strictDescentRigidPairColor C exponent hexp honeLoss
    (strictDescentRigidWordCarrier C exponent
      (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)) =
    strictDescentRigidPairColor C exponent hexp honeLoss
    (strictDescentRigidWordCarrier C exponent
      (netCollisionCertifiedReverseSource C exponent hexp honeLoss t)) at hcr
  have hcf := net_collision_equal_diagonal_same_lower_forward_colour_eq
    C exponent hexp honeLoss s t hdiag hb
  have hsupport :
      netCollisionCanonicalColourSupport C exponent hexp honeLoss s =
        netCollisionCanonicalColourSupport C exponent hexp honeLoss t := by
    unfold netCollisionCanonicalColourSupport
    rw [hcf, hcr]
  exact net_collision_canonical_support_fibre_injective
    C exponent hexp honeLoss s t hdiag hsupport

/-- A common target and the same UPPER endpoint-colour slot
likewise force the actual NET source word to be identical. -/
theorem net_collision_same_target_upper_slot_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss})
    (hdiag : netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t)
    (hslot : netCollisionCertifiedUpperColourSlot C exponent hexp honeLoss s =
      netCollisionCertifiedUpperColourSlot C exponent hexp honeLoss t) :
    s = t := by
  have hv := congrArg (fun z : V × Fin n => z.1) hslot
  have hcf := congrArg (fun z : V × Fin n => z.2) hslot
  change (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).2 =
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).2 at hv
  change transportablePairColor C
    (transportableWordCarrier C
      (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)) =
    transportablePairColor C
    (transportableWordCarrier C
      (netCollisionCertifiedForwardSource C exponent hexp honeLoss t)) at hcf
  have hcr := net_collision_equal_diagonal_same_upper_reverse_colour_eq
    C exponent hexp honeLoss s t hdiag hv
  have hsupport :
      netCollisionCanonicalColourSupport C exponent hexp honeLoss s =
        netCollisionCanonicalColourSupport C exponent hexp honeLoss t := by
    unfold netCollisionCanonicalColourSupport
    rw [hcf, hcr]
  exact net_collision_canonical_support_fibre_injective
    C exponent hexp honeLoss s t hdiag hsupport

/-- NEW vertex-cover capacity for the ACTUAL genuine NET source fibre
of a given diagonal target. For ANY lower slot subset A and upper slot
subset B, IF every eligible target bridge-colour edge meets A or B,
THEN its actual source fibre cardinal is ≤ |A|+|B|.

This is an explicit non-reused matching-payment certificate,
potentially stricter than min(|L*(d)|, |U*(d)|, |B_2(d)|).
The cover property is a NONTRIVIAL additional combinatorial obligation,
not a consequence of AngleCap as currently formalized. -/
theorem net_collision_target_fibre_card_le_exact_slot_vertex_cover
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool)
    (A B : Finset (V × Fin n))
    (hcover : ∀ e ∈ targetExactShellSlotEdges C exponent d,
      e.1 ∈ A ∨ e.2 ∈ B) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤
      A.card + B.card := by
  classical
  let S := {w : Fin n → Bool //
    w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}
  let F : Finset S :=
    netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d
  let left : S → V × Fin n :=
    netCollisionCertifiedLowerColourSlot C exponent hexp honeLoss
  let right : S → V × Fin n :=
    netCollisionCertifiedUpperColourSlot C exponent hexp honeLoss
  have hleft : ∀ s ∈ F, ∀ t ∈ F,
      left s = left t → s = t := by
    intro s hs t ht heq
    have hds : netCollisionCertifiedDiagonal C exponent hexp honeLoss s = d :=
      (Finset.mem_filter.mp hs).2
    have hdt : netCollisionCertifiedDiagonal C exponent hexp honeLoss t = d :=
      (Finset.mem_filter.mp ht).2
    exact net_collision_same_target_lower_slot_injective
      C exponent hexp honeLoss s t (hds.trans hdt.symm) heq
  have hright : ∀ s ∈ F, ∀ t ∈ F,
      right s = right t → s = t := by
    intro s hs t ht heq
    have hds : netCollisionCertifiedDiagonal C exponent hexp honeLoss s = d :=
      (Finset.mem_filter.mp hs).2
    have hdt : netCollisionCertifiedDiagonal C exponent hexp honeLoss t = d :=
      (Finset.mem_filter.mp ht).2
    exact net_collision_same_target_upper_slot_injective
      C exponent hexp honeLoss s t (hds.trans hdt.symm) heq
  have hactual : ∀ s ∈ F, left s ∈ A ∨ right s ∈ B := by
    intro s hs
    have hd : netCollisionCertifiedDiagonal C exponent hexp honeLoss s = d :=
      (Finset.mem_filter.mp hs).2
    have hedge :=
      net_collision_actual_pair_mem_exact_shell_slot_edges
        C exponent hexp honeLoss s
    rw [hd] at hedge
    exact hcover (left s, right s) hedge
  exact finset_two_injective_labels_card_le_cover
    F left right hleft hright A B hactual


/-- A FAMILY of exact-shell graph vertex covers (one for each ACTUALLY
hit canonical target) bounds the GLOBAL genuine NET duplicate-image
debt by the sum of those explicit NONREUSED cover excesses. The
cover property must be CHECKED, not silently assumed from AngleCap.
Unlike earlier min-of-pool capacities, this can exploit sparse
allowed edge incidence between exact lower/upper slots. -/
theorem net_collision_duplicate_debt_le_sum_exact_slot_cover_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (A B : (Fin n → Bool) → Finset (V × Fin n))
    (hcover : ∀ d ∈ netCollisionCertifiedDiagonalWords
      C exponent hexp honeLoss,
      ∀ e ∈ targetExactShellSlotEdges C exponent d,
      e.1 ∈ A d ∨ e.2 ∈ B d) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        ((A d).card + (B d).card - 1) := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_le_sum
  intro d hd
  have hfibre := net_collision_target_fibre_card_le_exact_slot_vertex_cover
    C exponent hexp honeLoss d (A d) (B d) (hcover d hd)
  omega

/-- The certified ACTUAL NET mobile forward/reverse hard mass remains
bounded by literal TRUE global Boolean holes plus singleton/soft
covered sinks, DISTINCT already-COVERED diagonals, and the explicit
NONREUSED exact-shell bipartite vertex-cover excess.

This is an exact legitimate reduction of the mobile payment obstacle,
NOT a proof that the vertex covers fit in independently unreserved
profile surplus, nor a payment of the remaining twin/mixed/soft terms.
-/
theorem net_mobile_mass_le_holes_covered_exact_slot_cover_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (A B : (Fin n → Bool) → Finset (V × Fin n))
    (hcover : ∀ d ∈ netCollisionCertifiedDiagonalWords
      C exponent hexp honeLoss,
      ∀ e ∈ targetExactShellSlotEdges C exponent d,
      e.1 ∈ A d ∨ e.2 ∈ B d) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
      (softOverlapCompletionWords C).card +
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card +
      (netCollisionCertifiedCoveredDiagonals C exponent hexp honeLoss).card +
      (∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        ((A d).card + (B d).card - 1)) := by
  have hmobile := net_mobile_mass_le_singleton_soft_holes_blockers_duplicates
    C exponent hexp honeLoss
  have hdup := net_collision_duplicate_debt_le_sum_exact_slot_cover_excess
    C exponent hexp honeLoss A B hcover
  omega

#print axioms net_collision_duplicate_debt_le_sum_exact_slot_cover_excess
#print axioms net_mobile_mass_le_holes_covered_exact_slot_cover_excess

#print axioms net_collision_actual_pair_mem_exact_shell_slot_edges
#print axioms target_exact_shell_edge_endpoints_mem_exact_colour_slots
#print axioms net_collision_same_target_lower_slot_injective
#print axioms net_collision_same_target_upper_slot_injective
#print axioms net_collision_target_fibre_card_le_exact_slot_vertex_cover

end OrderedEdgeColoring
end JSP000404Research
