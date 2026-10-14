import JSP000404Research.ResidualNetCollisionAllBitBridgeVertexSeparation
import Mathlib.Tactic

/-!
# ORIGINAL-centre vertex matching for target-exact actual NET sources

A slot matching in the target-exact eligible graph can still contain
two candidate edges that reuse the SAME ORIGINAL endpoint vertex
under different flip-colour slots. Such a slot matching is NOT
realizable by a genuinely duplicated NET source fibre: the previous
source-native HARD carrier matching proves that any two distinct
actual same-target source bridges have FOUR DISTINCT original
endpoints, for Hamming-two AND Hamming-four alike.

Define the tight candidate ORIGINAL bridge pool as the projection
of the already filtered exact-shell slot-edge graph, and take its
maximum vertex-disjoint original-bridge matching number.

Every actual target fibre has an exact-size original-centre
vertex-matching certificate inside that pool, giving a stronger
geometric exclusion gate than mere candidate slot matching.

The following condition is only a CONDITIONAL bridge to geometry:
all original target-eligible bridge pairs SHARE some vertex.
We do NOT claim the actual planar AngleCap enforces that condition.
When the condition IS established, duplicate debt vanishes and
the mobile ledger excludes its duplicate-image term. This does
not pay covered diagonals or any remaining six-source debts.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Project ONLY real source-compatible target-exact slot edges
onto their original lower/upper SOFT bridge endpoints. A graph
vertex is an ORIGINAL centre here, NOT a (centre,colour) slot. -/
noncomputable def targetExactShellOriginalBridgeEdges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool) : Finset (V × V) :=
  (targetExactShellSlotEdges C exponent d).image
    (fun e => (e.1.1, e.2.1))

/-- Every GENUINE NET source's selected SOFT bridge belongs to
the projected target-exact candidate edge pool at its own
certified canonical diagonal. -/
theorem net_collision_real_soft_bridge_mem_target_original_edges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) :
    netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s ∈
      targetExactShellOriginalBridgeEdges C exponent
        (netCollisionCertifiedDiagonal C exponent hexp honeLoss s) := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(netCollisionCertifiedLowerColourSlot
      C exponent hexp honeLoss s,
    netCollisionCertifiedUpperColourSlot
      C exponent hexp honeLoss s), ?_, ?_⟩
  · exact net_collision_actual_pair_mem_exact_shell_slot_edges
      C exponent hexp honeLoss s
  · rfl

/-- Pairwise vertex-disjoint eligible original bridges, preserving
the ORDERED original lower/upper centres. This differs from a
matching of slots (centre, colour). -/
def targetExactShellOriginalVertexMatching
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (M : Finset (V × V)) : Prop :=
  M ⊆ targetExactShellOriginalBridgeEdges C exponent d ∧
  ∀ p ∈ M, ∀ q ∈ M,
    (p.1 = q.1 ∨ p.1 = q.2 ∨
      p.2 = q.1 ∨ p.2 = q.2) → p = q

/-- Every GENUINE NET fixed-target source fibre has an original
soft-bridge VERTEX MATCHING of EXACTLY the same cardinality.
This is source-provenance-specific: not every candidate slot
matching need satisfy this stronger original-centre constraint. -/
theorem net_collision_target_fibre_has_exact_original_vertex_matching
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    ∃ M : Finset (V × V),
      targetExactShellOriginalVertexMatching C exponent d M ∧
      M.card =
        (netCollisionCertifiedDiagonalFibre
          C exponent hexp honeLoss d).card := by
  classical
  let S := {w : Fin n → Bool //
    w ∈ netActualForwardReverseCollisionWords
      C exponent hexp honeLoss}
  let F : Finset S :=
    netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d
  let E := {s : S // s ∈ F}
  let f : E → V × V :=
    fun s => netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s.1
  let M := (Finset.univ : Finset E).image f
  have htarget (s : E) :
      netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 = d :=
    (Finset.mem_filter.mp s.2).2
  have hinj : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    exact net_collision_same_bridge_same_diagonal_source_eq
      C exponent hexp honeLoss s.1 t.1
      ((htarget s).trans (htarget t).symm) h
  refine ⟨M, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hp
    have hmem :=
      net_collision_real_soft_bridge_mem_target_original_edges
        C exponent hexp honeLoss s.1
    rw [htarget s] at hmem
    exact hmem
  · intro p hp q hq hshare
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hq
    by_cases hst : s = t
    · rw [hst]
    · have hnone :=
        net_collision_distinct_same_target_no_shared_soft_bridge_vertex
          C exponent hexp honeLoss s.1 t.1
          ((htarget s).trans (htarget t).symm)
          (by
            intro heq
            exact hst (Subtype.ext heq))
      have hsourceShare : netCollisionBridgeOwnersShareVertex
          C exponent hexp honeLoss s.1 t.1 := by
        dsimp only [f] at hshare
        -- The vertex matching predicate orders the FOUR equality
        -- alternatives differently from netCollisionBridgeOwnersShareVertex.
        -- Reorder them explicitly rather than silently relying on change.
        rcases hshare with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inl h)
      exact False.elim (hnone hsourceShare)
  · change ((Finset.univ : Finset E).image f).card = F.card
    calc
      ((Finset.univ : Finset E).image f).card =
          (Finset.univ : Finset E).card :=
        Finset.card_image_of_injective _ hinj
      _ = F.card := by simp [E]

/-- Exact finite MAXIMUM number of pairwise original-vertex-disjoint
soft bridges in the eligible target-exact graph. No claim about
the value of this maximum is silently inserted. -/
noncomputable def targetExactShellOriginalVertexMatchingNumber
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset (V × V))).filter
    (targetExactShellOriginalVertexMatching C exponent d)).sup Finset.card

theorem target_exact_shell_original_vertex_matching_card_le_number
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (M : Finset (V × V))
    (hM : targetExactShellOriginalVertexMatching C exponent d M) :
    M.card ≤ targetExactShellOriginalVertexMatchingNumber
      C exponent d := by
  classical
  unfold targetExactShellOriginalVertexMatchingNumber
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM⟩

/-- Genuine fixed-target NET collision fibre has its own
ORIGINAL-CENTRE vertex matching capacity, distinct from the
eligible (vertex,colour) slot matching capacity. -/
theorem net_collision_fibre_card_le_original_vertex_matching_number
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre
      C exponent hexp honeLoss d).card ≤
    targetExactShellOriginalVertexMatchingNumber
      C exponent d := by
  obtain ⟨M, hM, hcard⟩ :=
    net_collision_target_fibre_has_exact_original_vertex_matching
      C exponent hexp honeLoss d
  rw [← hcard]
  exact target_exact_shell_original_vertex_matching_card_le_number
    C exponent d M hM

/-- Source-specific original vertex matching gives a new global
NET duplicate-image debt bound. It is an upper bound, NOT
an automatic true-hole or dyadic-surplus payment. -/
theorem net_collision_duplicate_debt_le_original_vertex_matching_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ d ∈ netCollisionCertifiedDiagonalWords
        C exponent hexp honeLoss,
        (targetExactShellOriginalVertexMatchingNumber
          C exponent d - 1) := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_le_sum
  intro d hd
  have hbound :=
    net_collision_fibre_card_le_original_vertex_matching_number
      C exponent hexp honeLoss d
  omega

/-- Pure candidate-bridge INTERSECTION property sufficient to
rule out NET repeated targets: for EVERY diagonal all projected
target-exact eligible original SOFT bridges meet at some original
vertex. The property is NOT derived from AngleCap here. -/
def AllTargetExactOriginalBridgesPairwiseIntersect
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Prop :=
  ∀ d : Fin n → Bool,
    ∀ p ∈ targetExactShellOriginalBridgeEdges C exponent d,
      ∀ q ∈ targetExactShellOriginalBridgeEdges C exponent d,
        p.1 = q.1 ∨ p.1 = q.2 ∨
          p.2 = q.1 ∨ p.2 = q.2

/-- CONDITIONAL zero-debt criterion that only needs the original
eligible bridge candidates to be vertex-intersecting. It does
NOT require that the more permissive colour-slot graph have
matching number <= 1, and no assumption is made about n or |V|. -/
theorem net_collision_duplicate_debt_zero_of_original_bridge_intersection
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hinter : AllTargetExactOriginalBridgesPairwiseIntersect
      C exponent) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss = 0 := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_eq_zero
  intro d hd
  obtain ⟨M, hM, hcard⟩ :=
    net_collision_target_fibre_has_exact_original_vertex_matching
      C exponent hexp honeLoss d
  have hsmall : M.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    exact hM.2 p hp q hq
      (hinter d p (hM.1 hp) q (hM.1 hq))
  omega

/-- The REAL mobile-hard ledger without repeated canonical target
debt under the independently checkable original-bridge geometric
intersection criterion. The covered diagonals and all other
six-source debts remain explicitly unpaid. -/
theorem net_mobile_mass_le_without_duplicates_of_original_bridge_intersection
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hinter : AllTargetExactOriginalBridgesPairwiseIntersect
      C exponent) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
      (softOverlapCompletionWords C).card +
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card +
      (netCollisionCertifiedCoveredDiagonals
        C exponent hexp honeLoss).card := by
  have hm := net_mobile_mass_le_singleton_soft_holes_blockers_duplicates
    C exponent hexp honeLoss
  have hz :=
    net_collision_duplicate_debt_zero_of_original_bridge_intersection
      C exponent hexp honeLoss hinter
  omega

#print axioms net_collision_target_fibre_has_exact_original_vertex_matching
#print axioms net_collision_fibre_card_le_original_vertex_matching_number
#print axioms net_collision_duplicate_debt_le_original_vertex_matching_excess
#print axioms net_collision_duplicate_debt_zero_of_original_bridge_intersection
#print axioms net_mobile_mass_le_without_duplicates_of_original_bridge_intersection

end OrderedEdgeColoring
end JSP000404Research
