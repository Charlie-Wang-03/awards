import JSP000404Research.ResidualGlobalSoftOverlapWordCharge
import JSP000404Research.ResidualCompletionPairAllocation
import Mathlib.Tactic

/-!
# Disjoint hard/soft partition of ALL Boolean completion overlaps

Every overlapping word has exactly ONE increasing residual carrier
edge, determined by its two covering vertices. Classify this carrier
as hard (same retained canonical codes) or soft (different codes).

The global overlap-word set is exactly the disjoint union of those
two parts. The new GLOBAL doubled-safe-flip word injection lands in
the soft part, and never in the hard part.

This is an EXACT partition and cross-pair injection, but still not a
payment of Boolean holes or profile losses. In particular replacing
the lower-branch admitted global-payment sorry using only this
decomposition would be circular.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Residual overlap edges with the SAME retained endpoint code. -/
noncomputable def hardOverlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (V × V) := by
  classical
  exact (overlapCarrierPairs C).filter
    (fun p => SameRetained C p.1 p.2)

@[simp] theorem mem_hardOverlapCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (p : V × V) :
    p ∈ hardOverlapCarrierPairs C ↔
      p ∈ overlapCarrierPairs C ∧
      SameRetained C p.1 p.2 := by
  classical
  simp [hardOverlapCarrierPairs]

/-- Overlap words whose unique residual carrier has equal endpoint codes. -/
noncomputable def hardOverlapCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (Fin n → Bool) :=
  (hardOverlapCarrierPairs C).biUnion
    (fun p => retainedCompletionWords C p.1 ∩ retainedCompletionWords C p.2)

/-- Hard and soft overlap WORDS are disjoint, not merely their
carrier edge labels: one word cannot have two different residual
carrier pairs because completion multiplicity is at most two. -/
theorem hard_soft_overlap_words_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Disjoint (hardOverlapCompletionWords C)
      (softOverlapCompletionWords C) := by
  classical
  rw [Finset.disjoint_left]
  intro word hhard hsoft
  obtain ⟨p,hp,hpword⟩ := Finset.mem_biUnion.mp hhard
  obtain ⟨q,hq,hqword⟩ := Finset.mem_biUnion.mp hsoft
  have hpdata := (mem_hardOverlapCarrierPairs C p).1 hp
  have hqdata := (mem_softOverlapCarrierPairs C q).1 hq
  have hporder : p.1 < p.2 :=
    ((mem_residualCarrierPairs C p.1 p.2).1
      ((mem_overlapCarrierPairs C p).1 hpdata.1).1).1
  have hqorder : q.1 < q.2 :=
    ((mem_residualCarrierPairs C q.1 q.2).1
      ((mem_overlapCarrierPairs C q).1 hqdata.1).1).1
  obtain ⟨hleft,hright⟩ :=
    completion_word_unique_ordered_pair C hporder hqorder
      (Finset.mem_inter.mp hpword).1
      (Finset.mem_inter.mp hpword).2
      (Finset.mem_inter.mp hqword).1
      (Finset.mem_inter.mp hqword).2
  have hpq : p = q := Prod.ext hleft hright
  exact hqdata.2 (hpq ▸ hpdata.2)

/-- Every completion overlap word has either a hard or a soft
carrier, with no third category. -/
theorem overlapCompletionWords_eq_hard_union_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    overlapCompletionWords C =
      hardOverlapCompletionWords C ∪
        softOverlapCompletionWords C := by
  classical
  rw [overlapCompletionWords_eq_overlapCarrier_biUnion C]
  ext word
  constructor
  · intro h
    obtain ⟨p,hpair,hword⟩ := Finset.mem_biUnion.mp h
    by_cases hsame : SameRetained C p.1 p.2
    · apply Finset.mem_union.mpr
      apply Or.inl
      unfold hardOverlapCompletionWords
      exact Finset.mem_biUnion.mpr
        ⟨p,(mem_hardOverlapCarrierPairs C p).2
          ⟨hpair,hsame⟩,hword⟩
    · apply Finset.mem_union.mpr
      apply Or.inr
      unfold softOverlapCompletionWords
      exact Finset.mem_biUnion.mpr
        ⟨p,(mem_softOverlapCarrierPairs C p).2
          ⟨hpair,hsame⟩,hword⟩
  · intro h
    rcases Finset.mem_union.mp h with hh | hs
    · obtain ⟨p,hp,hw⟩ := Finset.mem_biUnion.mp hh
      exact Finset.mem_biUnion.mpr
        ⟨p,((mem_hardOverlapCarrierPairs C p).1 hp).1,hw⟩
    · obtain ⟨p,hp,hw⟩ := Finset.mem_biUnion.mp hs
      exact Finset.mem_biUnion.mpr
        ⟨p,((mem_softOverlapCarrierPairs C p).1 hp).1,hw⟩

/-- Exact GLOBAL accounting identity: the hard and soft completion
overlap masses add without any duplicate word count. -/
theorem overlapCompletionWords_card_eq_hard_add_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (overlapCompletionWords C).card =
      (hardOverlapCompletionWords C).card +
        (softOverlapCompletionWords C).card := by
  rw [overlapCompletionWords_eq_hard_union_soft C]
  have hcard := Finset.card_union_add_card_inter
    (hardOverlapCompletionWords C) (softOverlapCompletionWords C)
  have hdisjoint := hard_soft_overlap_words_disjoint C
  have hinter :
      hardOverlapCompletionWords C ∩
        softOverlapCompletionWords C = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp hdisjoint
  rw [hinter] at hcard
  simpa using hcard

/-- The fully global hard-to-soft word injection cannot consume
hard-overlap words, because the two global overlap budgets are
genuinely disjoint. -/
theorem globally_doubled_hard_flip_soft_mass_bound
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (globalDoubledSafeFlips C).card +
      (hardOverlapCompletionWords C).card ≤
        (overlapCompletionWords C).card := by
  have hsoft :=
    globalDoubledSafeFlips_card_le_softOverlapWords C
  have hpartition := overlapCompletionWords_card_eq_hard_add_soft C
  omega

#print axioms hard_soft_overlap_words_disjoint
#print axioms overlapCompletionWords_eq_hard_union_soft
#print axioms overlapCompletionWords_card_eq_hard_add_soft
#print axioms globally_doubled_hard_flip_soft_mass_bound

end OrderedEdgeColoring
end JSP000404Research
