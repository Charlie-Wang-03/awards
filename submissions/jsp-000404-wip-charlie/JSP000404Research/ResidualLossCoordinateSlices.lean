import JSP000404Research.ResidualLossTranslatedConflict
import JSP000404Research.ResidualLocalCandidateCapacity
import Mathlib.Tactic

/-!
# Coordinate slices of translated projected-loss blocks

Fix an external choice of one retained flip coordinate for each vertex.
Projected-loss vertices whose chosen coordinate is the same c form a
coordinate slice.

Translated completion blocks inside one coordinate slice are pairwise
disjoint: translating all original loss cubes by the same Boolean involution
preserves their pairwise disjointness.

Therefore the cardinality of one translated slice is exactly the sum of the
individual translated-cube cardinalities.  At a projected-loss vertex that
cardinality is half of the target dyadic mass.

All loss--loss conflicts are consequently cross-coordinate conflicts.  The
separate translated-loss conflict theorem shows that every such cross-slice
intersection forces the connecting retained edge colour to equal one of the
two slice coordinates.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def lossCoordinateSlice
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (c : Fin n) : Finset V := by
  classical
  exact (projectedLossVertices C exponent).filter
    (fun v => choice v = c)

@[simp] theorem mem_lossCoordinateSlice
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (c : Fin n) (v : V) :
    v ∈ lossCoordinateSlice C exponent choice c ↔
      v ∈ projectedLossVertices C exponent ∧
      choice v = c := by
  classical
  simp [lossCoordinateSlice]

noncomputable def translatedLossSliceWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (c : Fin n) : Finset (Fin n → Bool) :=
  (lossCoordinateSlice C exponent choice c).biUnion
    (fun v => translatedCompletionWords C v c)

theorem translatedLossSlice_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (c : Fin n) :
    ((lossCoordinateSlice C exponent choice c : Finset V) : Set V).PairwiseDisjoint
        (fun v => translatedCompletionWords C v c) := by
  intro v hv w hw hvw
  have hvData :=
    (mem_lossCoordinateSlice C exponent choice c v).1 hv
  have hwData :=
    (mem_lossCoordinateSlice C exponent choice c w).1 hw
  exact translated_loss_blocks_disjoint_same_coordinate
    C exponent hexp honeLoss
    hvData.1 hwData.1 hvw c

theorem translatedLossSliceWords_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (c : Fin n) :
    (translatedLossSliceWords C exponent choice c).card =
      ∑ v ∈ lossCoordinateSlice C exponent choice c,
        (retainedCompletionWords C v).card := by
  classical
  unfold translatedLossSliceWords
  rw [Finset.card_biUnion
    (translatedLossSlice_pairwiseDisjoint
      C exponent hexp honeLoss choice c)]
  apply Finset.sum_congr rfl
  intro v hv
  exact translatedCompletionWords_card C v c

theorem projectedLoss_completion_card_eq_half_target
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent) :
    2 * (retainedCompletionWords C v).card =
      2 ^ exponent v := by
  have hlossEq :
      exponent v = projectedFree C v + 1 :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  rw [retainedCompletionWords_card, hlossEq, pow_succ]
  simp only [projectedFree]
  omega

theorem two_mul_translatedLossSliceWords_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (c : Fin n) :
    2 * (translatedLossSliceWords C exponent choice c).card =
      ∑ v ∈ lossCoordinateSlice C exponent choice c,
        2 ^ exponent v := by
  rw [translatedLossSliceWords_card
    C exponent hexp honeLoss choice c]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact projectedLoss_completion_card_eq_half_target
    C exponent
    ((mem_lossCoordinateSlice
      C exponent choice c v).1 hv).1

/-!
Summing over *all* retained coordinates counts each projected-loss vertex
exactly once. This is an exact identity for the sum of slice sizes, not
a disjointness assertion between different coordinate slices.
-/
theorem two_mul_total_translatedLossSliceWords_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n) :
    2 * (∑ c : Fin n,
      (translatedLossSliceWords C exponent choice c).card) =
      ∑ v ∈ projectedLossVertices C exponent,
        2 ^ exponent v := by
  classical
  calc
    2 * (∑ c : Fin n,
        (translatedLossSliceWords C exponent choice c).card) =
      ∑ c : Fin n,
        2 * (translatedLossSliceWords C exponent choice c).card := by
          rw [Finset.mul_sum]
    _ = ∑ c : Fin n,
          ∑ v ∈ lossCoordinateSlice C exponent choice c,
            2 ^ exponent v := by
          apply Finset.sum_congr rfl
          intro c hc
          exact two_mul_translatedLossSliceWords_card
            C exponent hexp honeLoss choice c
    _ = ∑ v ∈ projectedLossVertices C exponent,
          2 ^ exponent v := by
          simp only [lossCoordinateSlice, Finset.sum_filter]
          rw [Finset.sum_comm]
          simp

/-- If two different coordinate slices share an actual translated word,
then two distinct projected-loss centres are joined by a retained edge
whose colour is one of the two chosen flip coordinates. This records the
only possible cross-slice collision without assuming that it is absent. -/
theorem translatedLossSliceWords_cross_collision_edge_colour
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
    (hc : word ∈ translatedLossSliceWords C exponent choice c)
    (hd : word ∈ translatedLossSliceWords C exponent choice d) :
    ∃ v ∈ lossCoordinateSlice C exponent choice c,
      ∃ w ∈ lossCoordinateSlice C exponent choice d,
        v ≠ w ∧
          ((∃ hvwlt : v < w,
              ∃ hret : (C.color v w).val < n,
                retainedColor C v w hret = c ∨
                retainedColor C v w hret = d) ∨
           (∃ hwvlt : w < v,
              ∃ hret : (C.color w v).val < n,
                retainedColor C w v hret = c ∨
                retainedColor C w v hret = d)) := by
  classical
  obtain ⟨v, hv, hvWord⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨w, hw, hwWord⟩ := Finset.mem_biUnion.mp hd
  have hvData := (mem_lossCoordinateSlice C exponent choice c v).1 hv
  have hwData := (mem_lossCoordinateSlice C exponent choice d w).1 hw
  have hvw : v ≠ w := by
    intro heq
    subst w
    exact hcd (hvData.2.symm.trans hwData.2)
  refine ⟨v, hv, w, hw, hvw, ?_⟩
  exact translated_loss_conflict_edge_colour
    C exponent hexp honeLoss hvData.1 hwData.1
    hvw hvWord hwWord

#print axioms translatedLossSlice_pairwiseDisjoint
#print axioms translatedLossSliceWords_cross_collision_edge_colour
#print axioms two_mul_total_translatedLossSliceWords_card
#print axioms translatedLossSliceWords_card
#print axioms two_mul_translatedLossSliceWords_card

end OrderedEdgeColoring
end JSP000404Research
