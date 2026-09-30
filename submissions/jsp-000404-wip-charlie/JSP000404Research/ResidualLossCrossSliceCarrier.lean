import JSP000404Research.ResidualLossCrossSliceConflict
import Mathlib.Tactic

/-!
# Exact carrier decomposition of cross-coordinate loss conflicts

For two distinct translated-loss coordinate slices c and d, every common word
determines a unique loss vertex v from the c-slice and a unique loss vertex w
from the d-slice.

Define the cross-slice carrier pairs to be exactly those ordered pairs (v,w)
whose translated blocks intersect.  The corresponding pair-intersection word
sets are pairwise disjoint, and their disjoint union is exactly the full
cross-slice intersection.

Hence cross-coordinate translated-loss duplicate mass admits an exact
edge-by-edge decomposition, just like the residual overlap carrier
decomposition for the original completion cubes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def crossLossConflictPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (c d : Fin n) : Finset (V × V) := by
  classical
  exact
    ((lossCoordinateSlice C exponent choice c).product
      (lossCoordinateSlice C exponent choice d)).filter
      (fun p =>
        (translatedCompletionWords C p.1 c ∩
          translatedCompletionWords C p.2 d).Nonempty)

noncomputable def crossLossPairWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (c d : Fin n)
    (p : V × V) : Finset (Fin n → Bool) :=
  translatedCompletionWords C p.1 c ∩
    translatedCompletionWords C p.2 d

@[simp] theorem mem_crossLossConflictPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (c d : Fin n)
    (v w : V) :
    (v,w) ∈ crossLossConflictPairs C exponent choice c d ↔
      v ∈ lossCoordinateSlice C exponent choice c ∧
      w ∈ lossCoordinateSlice C exponent choice d ∧
      (translatedCompletionWords C v c ∩
        translatedCompletionWords C w d).Nonempty := by
  classical
  simp [crossLossConflictPairs]

theorem crossLossPairWords_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    {c d : Fin n}
    (hcd : c ≠ d) :
    ((crossLossConflictPairs C exponent choice c d :
        Finset (V × V)) : Set (V × V)).
      PairwiseDisjoint (crossLossPairWords C c d) := by
  intro p hp q hq hpq
  classical
  rw [Finset.disjoint_left]
  intro word hpWord hqWord
  have hpData :=
    (mem_crossLossConflictPairs
      C exponent choice c d p.1 p.2).1 hp
  have hqData :=
    (mem_crossLossConflictPairs
      C exponent choice c d q.1 q.2).1 hq
  have hpParts := Finset.mem_inter.mp hpWord
  have hqParts := Finset.mem_inter.mp hqWord

  have hfst :
      p.1 = q.1 :=
    translatedLossSlice_word_unique_vertex
      C exponent hexp honeLoss choice
      hpData.1 hqData.1 hpParts.1 hqParts.1
  have hsnd :
      p.2 = q.2 :=
    translatedLossSlice_word_unique_vertex
      C exponent hexp honeLoss choice
      hpData.2.1 hqData.2.1 hpParts.2 hqParts.2
  apply hpq
  exact Prod.ext hfst hsnd

theorem crossTranslatedLossSlice_inter_eq_biUnion_pairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (c d : Fin n) :
    translatedLossSliceWords C exponent choice c ∩
        translatedLossSliceWords C exponent choice d
      =
    (crossLossConflictPairs C exponent choice c d).biUnion
      (crossLossPairWords C c d) := by
  classical
  ext word
  constructor
  · intro hword
    have hparts := Finset.mem_inter.mp hword
    obtain ⟨v,hvSlice,hvWord⟩ :=
      Finset.mem_biUnion.mp hparts.1
    obtain ⟨w,hwSlice,hwWord⟩ :=
      Finset.mem_biUnion.mp hparts.2
    have hp :
        (v,w) ∈ crossLossConflictPairs
          C exponent choice c d := by
      apply (mem_crossLossConflictPairs
        C exponent choice c d v w).2
      exact ⟨hvSlice,hwSlice,
        ⟨word,hvWord,hwWord⟩⟩
    exact Finset.mem_biUnion.mpr
      ⟨(v,w),hp,Finset.mem_inter.mpr ⟨hvWord,hwWord⟩⟩
  · intro hword
    obtain ⟨p,hp,hpWord⟩ :=
      Finset.mem_biUnion.mp hword
    have hpData :=
      (mem_crossLossConflictPairs
        C exponent choice c d p.1 p.2).1 hp
    have hparts := Finset.mem_inter.mp hpWord
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_biUnion.mpr
        ⟨p.1,hpData.1,hparts.1⟩
    · exact Finset.mem_biUnion.mpr
        ⟨p.2,hpData.2.1,hparts.2⟩

theorem crossTranslatedLossSlice_inter_card_eq_sum_pairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    {c d : Fin n}
    (hcd : c ≠ d) :
    (translatedLossSliceWords C exponent choice c ∩
      translatedLossSliceWords C exponent choice d).card
      =
    ∑ p ∈ crossLossConflictPairs C exponent choice c d,
      (crossLossPairWords C c d p).card := by
  rw [crossTranslatedLossSlice_inter_eq_biUnion_pairs
    C exponent choice c d]
  rw [Finset.card_biUnion
    (crossLossPairWords_pairwiseDisjoint
      C exponent hexp honeLoss choice hcd)]

theorem crossLossConflictPair_edge_colour
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    {c d : Fin n}
    (hcd : c ≠ d)
    {p : V × V}
    (hp : p ∈ crossLossConflictPairs C exponent choice c d) :
    (∃ hvw : p.1 < p.2,
      ∃ hret : (C.color p.1 p.2).val < n,
        retainedColor C p.1 p.2 hret = c ∨
        retainedColor C p.1 p.2 hret = d)
    ∨
    (∃ hwv : p.2 < p.1,
      ∃ hret : (C.color p.2 p.1).val < n,
        retainedColor C p.2 p.1 hret = c ∨
        retainedColor C p.2 p.1 hret = d) := by
  have hpData :=
    (mem_crossLossConflictPairs
      C exponent choice c d p.1 p.2).1 hp
  obtain ⟨word,hvWord,hwWord⟩ := hpData.2.2
  have hvChoice :=
    ((mem_lossCoordinateSlice
      C exponent choice c p.1).1 hpData.1).2
  have hwChoice :=
    ((mem_lossCoordinateSlice
      C exponent choice d p.2).1 hpData.2.1).2
  have hne : p.1 ≠ p.2 := by
    intro h
    subst p
    rw [hvChoice] at hwChoice
    exact hcd hwChoice
  have hvLoss :=
    ((mem_lossCoordinateSlice
      C exponent choice c p.1).1 hpData.1).1
  have hwLoss :=
    ((mem_lossCoordinateSlice
      C exponent choice d p.2).1 hpData.2.1).1
  exact translated_loss_conflict_edge_colour
    C exponent hexp honeLoss
    hvLoss hwLoss hne hvWord hwWord

#print axioms crossLossPairWords_pairwiseDisjoint
#print axioms crossTranslatedLossSlice_inter_eq_biUnion_pairs
#print axioms crossTranslatedLossSlice_inter_card_eq_sum_pairs
#print axioms crossLossConflictPair_edge_colour

end OrderedEdgeColoring
end JSP000404Research
