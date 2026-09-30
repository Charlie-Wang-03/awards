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
    ((lossCoordinateSlice C exponent choice c : Finset V) : Set V).
      PairwiseDisjoint
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

#print axioms translatedLossSlice_pairwiseDisjoint
#print axioms translatedLossSliceWords_card
#print axioms two_mul_translatedLossSliceWords_card

end OrderedEdgeColoring
end JSP000404Research
