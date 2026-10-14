import JSP000404Research.ResidualNetCollisionCandidateShadowCompletion
import Mathlib.Tactic

/-!
# Candidate edges inject into ACTUAL soft-overlap completion shadow words

A target-compatible eligible bridge edge produces a Boolean
two-flip "shadow" word in BOTH of its original completion cubes.
Here we prove its bridge is genuinely an ordered SOFT overlap
carrier and use the prior at-most-two completion multiplicity
to show the shadow's original bridge pair is UNIQUE.

At a FIXED target d, the two exact singleton violation sets then
determine the two original flip colours from this bridge, so any
two candidate edges with the same shadow are equal.

Consequently every finite target-exact edge set embeds injectively
into the genuine COVERED soft-overlap word pool. It does NOT embed
into TRUE Boolean holes. Shadow words may be reused ACROSS DIFFERENT
targets d, so there is no asserted global non-reused payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The eligible candidate graph's underlying original bridge
is an oriented SOFT completion-overlap carrier, not merely an
arbitrary ordered vertex pair. -/
theorem target_exact_shell_edge_original_bridge_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (e : (V × Fin n) × (V × Fin n))
    (he : e ∈ targetExactShellSlotEdges C exponent d) :
    (e.1.1, e.2.1) ∈ softOverlapCarrierPairs C := by
  classical
  have hbridge :
      (e.1.1, e.2.1) ∈ targetDoubleShellTwoBitBridgeCarriers
        C exponent d := (Finset.mem_filter.mp he).2.1
  have htwo :
      (e.1.1,e.2.1) ∈ twoBitDisagreementBridgeCarriers
        C exponent := (Finset.mem_filter.mp hbridge).1
  have hinc :
      (e.1.1,e.2.1) ∈ incomparableBridgeSoftCarriers
        C exponent := (Finset.mem_filter.mp htwo).1
  have hfr :
      (e.1.1,e.2.1) ∈ forwardReverseBridgeSoftCarriers
        C exponent := (Finset.mem_filter.mp hinc).1
  exact (Finset.mem_filter.mp hfr).1

/-- The two-flip candidate shadow always belongs to the
ACTUAL soft overlap class, not just the larger covered word
class. Its original ordered soft bridge is an explicit witness. -/
theorem target_exact_shell_candidate_shadow_mem_soft_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (e : (V × Fin n) × (V × Fin n))
    (he : e ∈ targetExactShellSlotEdges C exponent d) :
    flipCompletionWord e.2.2 (flipCompletionWord e.1.2 d) ∈
      softOverlapCompletionWords C := by
  classical
  have hsoft := target_exact_shell_edge_original_bridge_soft
    C exponent d e he
  have hw := target_exact_shell_candidate_shadow_mem_both_endpoint_cubes
    C exponent d e he
  change
    flipCompletionWord e.2.2 (flipCompletionWord e.1.2 d) ∈
      retainedCompletionWords C e.1.1 ∧
    flipCompletionWord e.2.2 (flipCompletionWord e.1.2 d) ∈
      retainedCompletionWords C e.2.1 at hw
  exact Finset.mem_biUnion.mpr
    ⟨(e.1.1,e.2.1), hsoft, Finset.mem_inter.mpr hw⟩

/-- For a fixed canonical diagonal target, different candidate
graph edges have different ACTUAL soft completion shadow words.
Uses uniqueness of the TWO original soft bridge covering vertices
and the uniqueness of the active violating colour at EACH vertex.
No actual NET source provenance assumption is needed. -/
theorem target_exact_shell_candidate_shadow_injective_on_edges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (e f : (V × Fin n) × (V × Fin n))
    (he : e ∈ targetExactShellSlotEdges C exponent d)
    (hf : f ∈ targetExactShellSlotEdges C exponent d)
    (hshadow :
      flipCompletionWord e.2.2 (flipCompletionWord e.1.2 d) =
      flipCompletionWord f.2.2 (flipCompletionWord f.1.2 d)) :
    e = f := by
  classical
  have heSoft :=
    target_exact_shell_edge_original_bridge_soft C exponent d e he
  have hfSoft :=
    target_exact_shell_edge_original_bridge_soft C exponent d f hf
  have heOver := (mem_softOverlapCarrierPairs C (e.1.1,e.2.1)).1 heSoft
  have hfOver := (mem_softOverlapCarrierPairs C (f.1.1,f.2.1)).1 hfSoft
  have heOrder : e.1.1 < e.2.1 :=
    ((mem_residualCarrierPairs C e.1.1 e.2.1).1
      ((mem_overlapCarrierPairs C (e.1.1,e.2.1)).1 heOver.1).1).1
  have hfOrder : f.1.1 < f.2.1 :=
    ((mem_residualCarrierPairs C f.1.1 f.2.1).1
      ((mem_overlapCarrierPairs C (f.1.1,f.2.1)).1 hfOver.1).1).1
  have heCube := target_exact_shell_candidate_shadow_mem_both_endpoint_cubes
    C exponent d e he
  have hfCube := target_exact_shell_candidate_shadow_mem_both_endpoint_cubes
    C exponent d f hf
  change
    flipCompletionWord e.2.2 (flipCompletionWord e.1.2 d) ∈
      retainedCompletionWords C e.1.1 ∧
    flipCompletionWord e.2.2 (flipCompletionWord e.1.2 d) ∈
      retainedCompletionWords C e.2.1 at heCube
  change
    flipCompletionWord f.2.2 (flipCompletionWord f.1.2 d) ∈
      retainedCompletionWords C f.1.1 ∧
    flipCompletionWord f.2.2 (flipCompletionWord f.1.2 d) ∈
      retainedCompletionWords C f.2.1 at hfCube
  have hfLower :
      flipCompletionWord e.2.2 (flipCompletionWord e.1.2 d) ∈
        retainedCompletionWords C f.1.1 := by
    rw [hshadow]
    exact hfCube.1
  have hfUpper :
      flipCompletionWord e.2.2 (flipCompletionWord e.1.2 d) ∈
        retainedCompletionWords C f.2.1 := by
    rw [hshadow]
    exact hfCube.2
  have hpair := completion_word_unique_ordered_pair C
    heOrder hfOrder heCube.1 heCube.2 hfLower hfUpper
  have heData := (Finset.mem_filter.mp he).2
  have hfData := (Finset.mem_filter.mp hf).2
  have heBridge := (Finset.mem_filter.mp heData.1).2
  have hcardLower :
      (retainedActiveViolationCoords C e.1.1 d).card = 1 :=
    heBridge.1
  have hcardUpper :
      (retainedActiveViolationCoords C e.2.1 d).card = 1 :=
    heBridge.2.1
  have hcfF :
      f.2.2 ∈ retainedActiveViolationCoords C e.1.1 d := by
    rw [hpair.1]
    exact hfData.2.2.1
  have hcrF :
      f.1.2 ∈ retainedActiveViolationCoords C e.2.1 d := by
    rw [hpair.2]
    exact hfData.2.1
  have hcf : e.2.2 = f.2.2 := by
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcardLower
    have heq : e.2.2 = x := by
      have ht := heData.2.2.1
      rw [hx] at ht
      exact Finset.mem_singleton.mp ht
    have hfq : f.2.2 = x := by
      rw [hx] at hcfF
      exact Finset.mem_singleton.mp hcfF
    exact heq.trans hfq.symm
  have hcr : e.1.2 = f.1.2 := by
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcardUpper
    have heq : e.1.2 = x := by
      have ht := heData.2.2.1
      rw [hx] at ht
      exact Finset.mem_singleton.mp ht
    have hfq : f.1.2 = x := by
      rw [hx] at hcrF
      exact Finset.mem_singleton.mp hcrF
    exact heq.trans hfq.symm
  apply Prod.ext
  · exact Prod.ext hpair.1 hcr
  · exact Prod.ext hpair.2 hcf

/-- An unconditional target-specific graph-size bound, using a
genuine injective map to COVERED SOFT completion words. Since this
is target-by-target it is NOT an injection from all target-edge
pairs into globally distinct soft words. -/
theorem target_exact_shell_candidate_edges_card_le_soft_overlap_words
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool) :
    (targetExactShellSlotEdges C exponent d).card ≤
      (softOverlapCompletionWords C).card := by
  classical
  let E := targetExactShellSlotEdges C exponent d
  let g : {e : (V × Fin n) × (V × Fin n) // e ∈ E} →
      (Fin n → Bool) :=
    fun e => flipCompletionWord e.1.2.2
      (flipCompletionWord e.1.1.2 d)
  have hinj : Function.Injective g := by
    intro e f h
    apply Subtype.ext
    exact target_exact_shell_candidate_shadow_injective_on_edges
      C exponent d e.1 f.1 e.2 f.2 h
  have hsub :
      (Finset.univ : Finset {e : (V × Fin n) × (V × Fin n) // e ∈ E}).image g ⊆
      softOverlapCompletionWords C := by
    intro word hw
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hw
    exact target_exact_shell_candidate_shadow_mem_soft_overlap
      C exponent d e.1 e.2
  calc
    E.card =
        (Finset.univ : Finset
          {e : (V × Fin n) × (V × Fin n) // e ∈ E}).card := by simp
    _ = ((Finset.univ : Finset
          {e : (V × Fin n) × (V × Fin n) // e ∈ E}).image g).card := by
        symm
        exact Finset.card_image_of_injective _ hinj
    _ ≤ (softOverlapCompletionWords C).card :=
      Finset.card_le_card hsub

#print axioms target_exact_shell_edge_original_bridge_soft
#print axioms target_exact_shell_candidate_shadow_mem_soft_overlap
#print axioms target_exact_shell_candidate_shadow_injective_on_edges
#print axioms target_exact_shell_candidate_edges_card_le_soft_overlap_words

end OrderedEdgeColoring
end JSP000404Research
