import JSP000404Research.ResidualLossEarliestActualEdgeCarrier
import Mathlib.Tactic

/-!
# Exact global source-blocker decomposition of duplicate loss debt

Each later coordinate i assigns every recurring Boolean word to its
earliest earlier occurrence j. Within that ordered (i,j) pair, a
word determines a unique source-blocker pair among actual retained
edge carriers. The double indexing is exact, not an upper bound.

Even this decomposition does not give unused true Boolean holes,
nor prove the global six-source terminal payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Dyadic-free EXACT first-appearance collision cost of a
natural-coordinate pair; invalid indices contribute zero. -/
noncomputable def lossEarliestActualEdgeMassAtNat
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (i j : ℕ) : ℕ :=
  if hi : i < n then
    if hj : j < n then
      ∑ p ∈ crossLossConflictPairs C exponent choice
          ⟨i, hi⟩ ⟨j, hj⟩,
        (lossEarliestActualEdgeCarrier C exponent choice
          ⟨i, hi⟩ ⟨j, hj⟩ p).card
    else 0
  else 0

/-- Exact identity for the ORIGINAL loss duplicate debt. Every
contributing triple (i,j,p) contains an actual cross-coordinate
collision word, and p corresponds to a genuine retained edge.
No spurious holes or disjointness across later i are asserted. -/
theorem translatedLossDuplicateDebt_eq_sum_earliest_actual_edges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n) :
    translatedLossDuplicateDebt C exponent choice =
      ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range i,
          lossEarliestActualEdgeMassAtNat C exponent choice i j := by
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
  simpa [lossEarliestActualEdgeMassAtNat, hin, hjn] using
    (lossEarliestPairWords_card_eq_actualEdge_sum
      C exponent hexp honeLoss choice hcd)

#print axioms translatedLossDuplicateDebt_eq_sum_earliest_actual_edges

end OrderedEdgeColoring
end JSP000404Research
