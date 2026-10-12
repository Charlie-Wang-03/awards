import JSP000404Research.ResidualBridgeStrictUnusedLowerCapacity
import Mathlib.Tactic

/-!
# Strict-rigid lower-cube slack cannot contain ANY hard overlap

Previous work proved that the unused lower-cube slots U := L \ R
are covered, disjoint from reverse strict-rigid hard source words,
and have exactly the strict target-exponent descent-gap cardinality.

This module proves a stronger classification: U is disjoint from
ALL hard-overlap completion words, including already-paid hard faces,
ascending/descending mixed-rigid faces, and twin hard faces.

The argument is global, not merely a disjointness from R: each word
in a residual LOWER cube uniquely determines its lower source vertex;
two hard carriers with that shared vertex must agree by hard-carrier
vertex matching. Thus any hard word in a strict lower cube would
already lie in its original strict-rigid source face R.

As a consequence the unused lower-cube slots can only be SINGLETON
covered or SOFT overlapped. These are all COVERED destinations.
This theorem does not provide true Boolean holes or unreserved surplus.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Even hard source faces OTHER than the strict-rigid source are excluded
from unused strict lower cubes. -/
theorem unused_strict_lower_words_disjoint_all_hard_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Disjoint (netStrictRigidUnusedLowerWords C exponent)
      (hardOverlapCompletionWords C) := by
  classical
  apply Finset.disjoint_left.mpr
  intro word hunused hhard
  have hunused' :
      word ∈ netStrictRigidLowerCapacityWords C exponent \
        netStrictDescentRigidWords C exponent := hunused
  have hlower := (Finset.mem_sdiff.mp hunused').1
  change word ∈
    (netStrictDescentRigidCarriers C exponent).biUnion
      (fun p => retainedCompletionWords C p.1) at hlower
  obtain ⟨p, hp, hpword⟩ := Finset.mem_biUnion.mp hlower
  obtain ⟨q, hq, hqword⟩ := Finset.mem_biUnion.mp hhard
  have hpNet :=
    ((mem_netStrictDescentRigidCarriers C exponent p).1 hp).1
  have hpHard :=
    ((mem_netUnpaidHardCarrierPairs C exponent p).1
      ((mem_netRigidHardCarriers C exponent p).1 hpNet).1).1
  have hpRes : p.1 < p.2 ∧ IsResidual C p.1 p.2 :=
    (mem_residualCarrierPairs C p.1 p.2).1
      ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1 hpHard).1).1
  have hqRes : q.1 < q.2 ∧ IsResidual C q.1 q.2 :=
    (mem_residualCarrierPairs C q.1 q.2).1
      ((mem_overlapCarrierPairs C q).1
        ((mem_hardOverlapCarrierPairs C q).1 hq).1).1
  have heqLower : p.1 = q.1 :=
    residual_lower_completion_word_unique C
      hpRes.1 hqRes.1 hpRes.2 hqRes.2
      hpword (Finset.mem_inter.mp hqword).1
  have hpq : p = q :=
    hard_carrier_shared_endpoint_implies_same_pair
      C hpHard hq (Or.inl heqLower)
  have hrigid : word ∈ netStrictDescentRigidWords C exponent := by
    unfold netStrictDescentRigidWords
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hp, ?_⟩
    simpa only [hpq] using hqword
  exact (Finset.mem_sdiff.mp hunused').2 hrigid

/-- No hard face is present in the unused lower-cube slack. The
only possible covered classes are singleton words and soft overlaps. -/
theorem unused_strict_lower_words_subset_singleton_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    netStrictRigidUnusedLowerWords C exponent ⊆
      singletonCompletionWords C ∪ softOverlapCompletionWords C := by
  classical
  intro word hw
  have hcovered : word ∈ coveredCompletionWords C :=
    unused_strict_lower_words_subset_covered C exponent hw
  have hnotHard : word ∉ hardOverlapCompletionWords C := by
    intro hh
    exact (Finset.disjoint_left.mp
      (unused_strict_lower_words_disjoint_all_hard_overlap
        C exponent)) hw hh
  have hnonempty : (completionFibre C word).Nonempty :=
    (mem_coveredCompletionWords C word).1 hcovered
  have hpos : 0 < (completionFibre C word).card :=
    Finset.card_pos.mpr hnonempty
  have hle : (completionFibre C word).card ≤ 2 :=
    completionFibre_card_le_two C word
  by_cases hone : (completionFibre C word).card = 1
  · exact Finset.mem_union.mpr
      (Or.inl ((mem_singletonCompletionWords C word).2 hone))
  · have htwo : (completionFibre C word).card = 2 := by omega
    have hoverlap : word ∈ overlapCompletionWords C :=
      (mem_overlapCompletionWords C word).2 htwo
    rw [overlapCompletionWords_eq_hard_union_soft C] at hoverlap
    rcases Finset.mem_union.mp hoverlap with hh | hs
    · exact False.elim (hnotHard hh)
    · exact Finset.mem_union.mpr (Or.inr hs)

#print axioms unused_strict_lower_words_disjoint_all_hard_overlap
#print axioms unused_strict_lower_words_subset_singleton_soft

end OrderedEdgeColoring
end JSP000404Research
