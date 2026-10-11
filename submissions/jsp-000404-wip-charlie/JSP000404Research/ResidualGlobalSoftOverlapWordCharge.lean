import JSP000404Research.ResidualGlobalSafeFlipMatching
import JSP000404Research.ResidualCompletionPairAllocation
import Mathlib.Tactic

/-!
# Globally injective hard-to-soft overlap WORD displacement

Previously, doubled safe flips over ALL same-retained source pairs
were globally injected into soft residual-overlap CARRIER EDGES.

We now show that distinct source triples have distinct ACTUAL Boolean
flip words, each doubly covered by the unique target soft carrier.
Thus doubled safe flips inject into soft-overlap Boolean words, not
merely a count of target residual edges.

The new words are *covered* and therefore cannot be counted as
Boolean holes. This is a global overlap-to-overlap transfer,
not a proof of the open completion-defect payment inequality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Globally doubly covered words whose unique carrier residual edge
has distinct canonical retained endpoint codes. -/
noncomputable def softOverlapCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (Fin n → Bool) :=
  (softOverlapCarrierPairs C).biUnion
    (fun p => retainedCompletionWords C p.1 ∩ retainedCompletionWords C p.2)

/-- For every doubled safe flip, the upper endpoint v covers its
flipped word, even though the original lower endpoint a does not. -/
theorem globalDoubledSafeFlip_upper_completion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (x : {y : (V × V) × Fin n // y ∈ globalDoubledSafeFlips C}) :
    flippedRetainedCode C x.1.1.1 x.1.2 ∈
      retainedCompletionWords C x.1.1.2 := by
  have hd := (mem_globalDoubledSafeFlips C x.1).1 x.2
  have hc := (mem_doubleSafeFlipColors C
    x.1.1.1 x.1.1.2 x.1.2).1 hd.2.2
  exact sameRetained_flip_mem_inactive_upper_cube
    C x.1.1.1 x.1.1.2 x.1.2 hd.2.1 hc.2.1

/-- The global safe-flip word is always an actually doubly covered
SOFT overlap word, witnessed by its injected target residual edge. -/
theorem globalDoubledSafeFlip_mem_soft_overlap_words
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (x : {y : (V × V) × Fin n // y ∈ globalDoubledSafeFlips C}) :
    flippedRetainedCode C x.1.1.1 x.1.2 ∈
      softOverlapCompletionWords C := by
  classical
  let w := globalDoubledSafeFlipBlocker C x
  let v := x.1.1.2
  have hblock := globalDoubledSafeFlipBlocker_spec C x
  have hpair := (globalDoubledSafeFlipSoftOverlapEdge C x).2
  change (w,v) ∈ softOverlapCarrierPairs C at hpair
  unfold softOverlapCompletionWords
  apply Finset.mem_biUnion.mpr
  refine ⟨(w,v),hpair,?_⟩
  exact Finset.mem_inter.mpr
    ⟨hblock.2.2.2.2,globalDoubledSafeFlip_upper_completion C x⟩

/-- Subtype-valued map from all doubly covered global safe flips
to genuine SOFT overlap Boolean words. -/
noncomputable def globalDoubledSafeFlipToSoftWord
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    {x : (V × V) × Fin n // x ∈ globalDoubledSafeFlips C} →
      {word : Fin n → Bool // word ∈ softOverlapCompletionWords C} :=
  fun x => ⟨flippedRetainedCode C x.1.1.1 x.1.2,
    globalDoubledSafeFlip_mem_soft_overlap_words C x⟩

/-- This WORD map is globally injective, even across different
source same-retained pairs. Equal Boolean flipped words would share
the same unique residual completion carrier, and carrier injectivity
recovers the entire (a,v,c) source triple. -/
theorem globalDoubledSafeFlipToSoftWord_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Function.Injective (globalDoubledSafeFlipToSoftWord C) := by
  classical
  intro x y hwordEq
  have hw :
      flippedRetainedCode C x.1.1.1 x.1.2 =
      flippedRetainedCode C y.1.1.1 y.1.2 :=
    congrArg Subtype.val hwordEq
  have hxSpec := globalDoubledSafeFlipBlocker_spec C x
  have hySpec := globalDoubledSafeFlipBlocker_spec C y
  have hyW : flippedRetainedCode C x.1.1.1 x.1.2 ∈
      retainedCompletionWords C (globalDoubledSafeFlipBlocker C y) := by
    rw [hw]
    exact hySpec.2.2.2.2
  have hyV : flippedRetainedCode C x.1.1.1 x.1.2 ∈
      retainedCompletionWords C y.1.1.2 := by
    rw [hw]
    exact globalDoubledSafeFlip_upper_completion C y
  obtain ⟨hblockers,hupper⟩ :=
    completion_word_unique_ordered_pair C
      hxSpec.2.1 hySpec.2.1
      hxSpec.2.2.2.2
      (globalDoubledSafeFlip_upper_completion C x)
      hyW hyV
  apply globalDoubledSafeFlipOverlapEdge_injective C
  apply Subtype.ext
  exact Prod.ext hblockers hupper

/-- Certified GLOBAL count of source doubled safe flips by genuinely
non-hard, doubly-covered Boolean words. The target words are NOT
uncovered holes and cannot be charged as such. -/
theorem globalDoubledSafeFlips_card_le_softOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (globalDoubledSafeFlips C).card ≤
      (softOverlapCompletionWords C).card := by
  classical
  have h := Fintype.card_le_of_injective
    (globalDoubledSafeFlipToSoftWord C)
    (globalDoubledSafeFlipToSoftWord_injective C)
  simpa only [Fintype.card_coe] using h

#print axioms globalDoubledSafeFlip_upper_completion
#print axioms globalDoubledSafeFlip_mem_soft_overlap_words
#print axioms globalDoubledSafeFlipToSoftWord_injective
#print axioms globalDoubledSafeFlips_card_le_softOverlapWords

end OrderedEdgeColoring
end JSP000404Research
