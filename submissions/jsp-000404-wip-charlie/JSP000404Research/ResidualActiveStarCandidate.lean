import JSP000404Research.ResidualLossTranslatedBlock
import Mathlib.Tactic

/-!
# Disjoint Hamming stars around one completion cube

Let Q_v be one retained completion cube and let c,d be two distinct retained
active coordinates at v.

The translated cubes flip_c(Q_v) and flip_d(Q_v) are disjoint.  At coordinate
c the first translated cube has the opposite canonical bit, while the second
translation leaves c unchanged.

Consequently the original cube together with all one-active-coordinate
translates forms a disjoint Hamming star.  Its cardinality is exactly

  (1 + card(retainedActive(v))) * card(Q_v).

For a projected-loss vertex this provides a much richer Hall candidate block
than a single doubled completion block.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem translatedCompletionWords_disjoint_of_distinct_active
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {c d : Fin n}
    (hc : c ∈ retainedActive C v)
    (hd : d ∈ retainedActive C v)
    (hcd : c ≠ d) :
    Disjoint
      (translatedCompletionWords C v c)
      (translatedCompletionWords C v d) := by
  classical
  rw [Finset.disjoint_left]
  intro word hcWord hdWord
  have hcOrig :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 hcWord
  have hdOrig :
      flipBoolWordAt word d ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v d word).1 hdWord
  have hcComp :=
    (mem_retainedCompletionWords C v
      (flipBoolWordAt word c)).1 hcOrig
  have hdComp :=
    (mem_retainedCompletionWords C v
      (flipBoolWordAt word d)).1 hdOrig
  have hcAt := hcComp c hc
  have hdAt := hdComp c hc
  rw [flipBoolWordAt_at] at hcAt
  rw [flipBoolWordAt_off word hcd] at hdAt
  rw [hdAt] at hcAt
  cases h : retainedBit C v c <;> simp [h] at hcAt

theorem translatedCompletionWords_active_family_pairwiseDisjoint
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    ((retainedActive C v : Finset (Fin n)) : Set (Fin n)).
      PairwiseDisjoint
        (fun c => translatedCompletionWords C v c) := by
  intro c hc d hd hcd
  exact translatedCompletionWords_disjoint_of_distinct_active
    C hc hd hcd

noncomputable def allActiveTranslatedWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) : Finset (Fin n → Bool) :=
  (retainedActive C v).biUnion
    (fun c => translatedCompletionWords C v c)

theorem allActiveTranslatedWords_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    (allActiveTranslatedWords C v).card =
      (retainedActive C v).card *
        (retainedCompletionWords C v).card := by
  classical
  unfold allActiveTranslatedWords
  rw [Finset.card_biUnion
    (translatedCompletionWords_active_family_pairwiseDisjoint C v)]
  calc
    (∑ c ∈ retainedActive C v,
      (translatedCompletionWords C v c).card)
        =
      ∑ _c ∈ retainedActive C v,
        (retainedCompletionWords C v).card := by
          apply Finset.sum_congr rfl
          intro c hc
          exact translatedCompletionWords_card C v c
    _ =
      (retainedActive C v).card *
        (retainedCompletionWords C v).card := by
          simp

theorem original_disjoint_allActiveTranslatedWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    Disjoint
      (retainedCompletionWords C v)
      (allActiveTranslatedWords C v) := by
  classical
  rw [Finset.disjoint_left]
  intro word hQ hT
  obtain ⟨c,hc,hcT⟩ := Finset.mem_biUnion.mp hT
  exact Finset.disjoint_left.mp
    (translatedCompletionWords_disjoint_original_of_active C hc)
    hcT hQ

noncomputable def activeStarCandidateBlock
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) : Finset (Fin n → Bool) :=
  retainedCompletionWords C v ∪
    allActiveTranslatedWords C v

theorem activeStarCandidateBlock_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    (activeStarCandidateBlock C v).card =
      ((retainedActive C v).card + 1) *
        (retainedCompletionWords C v).card := by
  classical
  unfold activeStarCandidateBlock
  rw [Finset.card_union_of_disjoint
    (original_disjoint_allActiveTranslatedWords C v)]
  rw [allActiveTranslatedWords_card]
  omega

#print axioms translatedCompletionWords_disjoint_of_distinct_active
#print axioms allActiveTranslatedWords_card
#print axioms activeStarCandidateBlock_card

end OrderedEdgeColoring
end JSP000404Research
