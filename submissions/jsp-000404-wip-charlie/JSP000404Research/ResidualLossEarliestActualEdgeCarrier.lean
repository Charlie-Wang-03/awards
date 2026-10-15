import JSP000404Research.ResidualLossEarliestCollision
import Mathlib.Tactic

/-!
# Exact first-appearance loss duplicate debt on REAL retained edges

For fixed distinct loss coordinates c and d, each word in their
translated-slice intersection uniquely belongs to an actual source/
blocker pair. Restrict to words NOT appearing before d; disjointness
within this fixed pair survives restriction.

The final global duplicate debt is counted exactly across later
coordinates i and their earliest predecessor j, and therefore has
an exact triple-index finite carrier decomposition. This is still
an accounting theorem, not payment into true holes or surplus.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Actual intersecting pair words for coordinates c,d which are
seen at coordinate d for the FIRST time. -/
noncomputable def lossEarliestActualEdgePairWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (c d : Fin n) (p : V × V) :
    Finset (Fin n → Bool) :=
  crossLossPairWords C c d p \
    lossPrefixUnion (lossSliceAtNat C exponent choice) d.val

/-- The exact (c,d) first-predecessor collision set is the
union of true source/blocker *edge* intersection carriers cut
by the prefix prior to d. -/
theorem lossEarliestPair_eq_actualEdge_biUnion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (c d : Fin n) :
    lossEarliestPairWords
        (lossSliceAtNat C exponent choice) c.val d.val =
      (crossLossConflictPairs C exponent choice c d).biUnion
        (lossEarliestActualEdgePairWords C exponent choice c d) := by
  classical
  have hc :
      lossSliceAtNat C exponent choice c.val =
        translatedLossSliceWords C exponent choice c := by
    simp [lossSliceAtNat, c.isLt]
  have hd :
      lossSliceAtNat C exponent choice d.val =
        translatedLossSliceWords C exponent choice d := by
    simp [lossSliceAtNat, d.isLt]
  unfold lossEarliestPairWords lossEarliestActualEdgePairWords
  rw [hc, hd,
    crossTranslatedLossSlice_inter_eq_biUnion_pairs C exponent choice c d]
  ext word
  simp only [Finset.mem_sdiff, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨p, hp, hword⟩, hnot⟩
    exact ⟨p, hp, ⟨hword, hnot⟩⟩
  · rintro ⟨p, hp, ⟨hword, hnot⟩⟩
    exact ⟨⟨p, hp, hword⟩, hnot⟩

/-- Exact cardinal sum over true distinct source/blocker carriers
for one earliest-prior-coordinate slice. No edge carrier repeats a
Boolean word WITHIN this (c,d) coordinate pair. -/
theorem lossEarliestPair_card_eq_actualEdge_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (c d : Fin n) (hcd : c ≠ d) :
    (lossEarliestPairWords
      (lossSliceAtNat C exponent choice) c.val d.val).card =
      ∑ p ∈ crossLossConflictPairs C exponent choice c d,
        (lossEarliestActualEdgePairWords
          C exponent choice c d p).card := by
  classical
  rw [lossEarliestPair_eq_actualEdge_biUnion C exponent choice c d]
  have hpair :=
    crossLossPairWords_pairwiseDisjoint
      C exponent hexp honeLoss choice hcd
  have hdisj :
      (((crossLossConflictPairs C exponent choice c d :
          Finset (V × V)) : Set (V × V))).PairwiseDisjoint
        (lossEarliestActualEdgePairWords C exponent choice c d) := by
    intro p hp q hq hpq
    have h0 := hpair hp hq hpq
    change Disjoint
      (lossEarliestActualEdgePairWords C exponent choice c d p)
      (lossEarliestActualEdgePairWords C exponent choice c d q)
    rw [Finset.disjoint_left]
    intro word hwp hwq
    exact Finset.disjoint_left.mp h0
      (Finset.mem_sdiff.mp hwp).1
      (Finset.mem_sdiff.mp hwq).1
  exact Finset.card_biUnion hdisj

/-- Full original duplicate debt as an EXACT, finite,
earliest-coordinate / earliest actual-edge source-blocker pair sum.
Only actually intersecting words and genuine retained edge carriers
enter the expression; no true-hole credit has been assumed. -/
theorem translatedLossDuplicateDebt_eq_earliestActualEdge_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n) :
    translatedLossDuplicateDebt C exponent choice =
      ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range i,
          ∑ p ∈ crossLossConflictPairs C exponent choice
              ⟨i, by omega⟩ ⟨j, by omega⟩,
            (lossEarliestActualEdgePairWords C exponent choice
              ⟨i, by omega⟩ ⟨j, by omega⟩ p).card := by
  classical
  rw [translatedLossDuplicateDebt_eq_sum_earliestPairWords]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hin : i < n := Finset.mem_range.mp hi
  have hji : j < i := Finset.mem_range.mp hj
  have hjn : j < n := lt_trans hji hin
  have hcd : (⟨i, hin⟩ : Fin n) ≠ ⟨j, hjn⟩ := by
    intro h
    have hv : i = j := by
      simpa only [Fin.val_mk] using congrArg Fin.val h
    omega
  simpa using
    (lossEarliestPair_card_eq_actualEdge_sum
      C exponent hexp honeLoss choice
      ⟨i, hin⟩ ⟨j, hjn⟩ hcd)

#print axioms lossEarliestPair_eq_actualEdge_biUnion
#print axioms lossEarliestPair_card_eq_actualEdge_sum
#print axioms translatedLossDuplicateDebt_eq_earliestActualEdge_sum

end OrderedEdgeColoring
end JSP000404Research
