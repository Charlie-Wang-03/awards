import JSP000404Research.ResidualLossCoordinateSlices
import Mathlib.Tactic

/-!
# Unique carrier pairs for cross-coordinate translated-loss conflicts

Inside one translated-loss coordinate slice the blocks are pairwise disjoint.
Therefore a word in that slice determines a unique loss vertex.

For two distinct coordinates c and d, every word in the intersection of the
two translated slice unions consequently determines a unique ordered pair of
loss vertices (v,w), one from each slice.  The translated-loss conflict theorem
then forces the retained edge colour between v and w to be c or d.

Thus cross-slice duplicate mass decomposes exactly by a family of vertex-pair
carriers, analogous to the residual overlap carrier decomposition for the
original completion cubes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem translatedLossSlice_word_unique_vertex
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    {c : Fin n}
    {word : Fin n → Bool}
    {v w : V}
    (hv : v ∈ lossCoordinateSlice C exponent choice c)
    (hw : w ∈ lossCoordinateSlice C exponent choice c)
    (hvWord : word ∈ translatedCompletionWords C v c)
    (hwWord : word ∈ translatedCompletionWords C w c) :
    v = w := by
  by_contra hvw
  have hdisj :=
    translatedLossSlice_pairwiseDisjoint
      C exponent hexp honeLoss choice c
      hv hw hvw
  exact Finset.disjoint_left.mp hdisj hvWord hwWord

theorem crossTranslatedLossSlice_word_has_unique_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    {c d : Fin n}
    (hcd : c ≠ d)
    {word : Fin n → Bool}
    (hword :
      word ∈
        translatedLossSliceWords C exponent choice c ∩
        translatedLossSliceWords C exponent choice d) :
    ∃ v w : V,
      v ∈ lossCoordinateSlice C exponent choice c ∧
      w ∈ lossCoordinateSlice C exponent choice d ∧
      v ≠ w ∧
      word ∈ translatedCompletionWords C v c ∧
      word ∈ translatedCompletionWords C w d ∧
      (∀ v' : V,
        v' ∈ lossCoordinateSlice C exponent choice c →
        word ∈ translatedCompletionWords C v' c →
        v' = v) ∧
      (∀ w' : V,
        w' ∈ lossCoordinateSlice C exponent choice d →
        word ∈ translatedCompletionWords C w' d →
        w' = w) := by
  have hparts := Finset.mem_inter.mp hword
  obtain ⟨v,hvSlice,hvWord⟩ :=
    Finset.mem_biUnion.mp hparts.1
  obtain ⟨w,hwSlice,hwWord⟩ :=
    Finset.mem_biUnion.mp hparts.2
  have hvChoice :=
    ((mem_lossCoordinateSlice
      C exponent choice c v).1 hvSlice).2
  have hwChoice :=
    ((mem_lossCoordinateSlice
      C exponent choice d w).1 hwSlice).2
  have hvw : v ≠ w := by
    intro h
    subst w
    rw [hvChoice] at hwChoice
    exact hcd hwChoice
  refine ⟨v,w,hvSlice,hwSlice,hvw,hvWord,hwWord,?_,?_⟩
  · intro v' hv'Slice hv'Word
    exact translatedLossSlice_word_unique_vertex
      C exponent hexp honeLoss choice
      hv'Slice hvSlice hv'Word hvWord
  · intro w' hw'Slice hw'Word
    exact translatedLossSlice_word_unique_vertex
      C exponent hexp honeLoss choice
      hw'Slice hwSlice hw'Word hwWord

theorem crossTranslatedLossSlice_conflict_edge_colour
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    {c d : Fin n}
    (hcd : c ≠ d)
    {word : Fin n → Bool}
    (hword :
      word ∈
        translatedLossSliceWords C exponent choice c ∩
        translatedLossSliceWords C exponent choice d) :
    ∃ v w : V,
      v ∈ lossCoordinateSlice C exponent choice c ∧
      w ∈ lossCoordinateSlice C exponent choice d ∧
      v ≠ w ∧
      word ∈ translatedCompletionWords C v c ∧
      word ∈ translatedCompletionWords C w d ∧
      (
        (∃ hvw : v < w,
          ∃ hret : (C.color v w).val < n,
            retainedColor C v w hret = c ∨
            retainedColor C v w hret = d)
        ∨
        (∃ hwv : w < v,
          ∃ hret : (C.color w v).val < n,
            retainedColor C w v hret = c ∨
            retainedColor C w v hret = d)
      ) := by
  obtain ⟨v,w,hvSlice,hwSlice,hvw,
      hvWord,hwWord,_hvUniq,_hwUniq⟩ :=
    crossTranslatedLossSlice_word_has_unique_pair
      C exponent hexp honeLoss choice hcd hword
  have hvLoss :=
    ((mem_lossCoordinateSlice
      C exponent choice c v).1 hvSlice).1
  have hwLoss :=
    ((mem_lossCoordinateSlice
      C exponent choice d w).1 hwSlice).1
  have hedge :=
    translated_loss_conflict_edge_colour
      C exponent hexp honeLoss
      hvLoss hwLoss hvw hvWord hwWord
  exact ⟨v,w,hvSlice,hwSlice,hvw,
    hvWord,hwWord,hedge⟩

#print axioms translatedLossSlice_word_unique_vertex
#print axioms crossTranslatedLossSlice_word_has_unique_pair
#print axioms crossTranslatedLossSlice_conflict_edge_colour

end OrderedEdgeColoring
end JSP000404Research
