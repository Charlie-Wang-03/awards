import JSP000404Research.ResidualLossPairwiseOvercount
import Mathlib.Tactic

/-!
# Dyadic upper budget for the actual projected-loss duplicate debt

The already exact cross-coordinate carrier decomposition and min-dyadic
bound can now be assembled over all natural-index coordinate pairs
without reusing any coordinate PAIR. The same Boolean word may still
belong to multiple pairwise intersections. We need only an upper bound,
so such further overcount is conservative, not an assumed disjointness.

This is NOT an injection of debt into genuine unused holes, and it
does not close the remaining terminal six-source payment obligation.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Real pairwise cross-coordinate carrier budget, indexed by two
natural indices. Values outside the retained Fin n palette give 0. -/
noncomputable def lossPairwiseActualEdgeDyadicCostAtNat
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (i j : ℕ) : ℕ :=
  if hi : i < n then
    if hj : j < n then
      ∑ p ∈ crossLossConflictPairs C exponent choice
          ⟨i, hi⟩ ⟨j, hj⟩,
        min (2 ^ projectedFree C p.1)
            (2 ^ projectedFree C p.2)
    else 0
  else 0

/-- Every actual loss-duplicate debt word is bounded by a
conservative sum of capacities over ONLY TRUE pair-conflict edges,
with each coordinate pair j<i counted exactly once. -/
theorem translatedLossDuplicateDebt_le_actualEdge_dyadic_pairBudget
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n) :
    translatedLossDuplicateDebt C exponent choice ≤
      ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range i,
          lossPairwiseActualEdgeDyadicCostAtNat
            C exponent choice i j := by
  classical
  have hdup :=
    translatedLossDuplicateDebt_le_pairwise_slices
      C exponent choice
  apply le_trans hdup
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  have hin : i < n := Finset.mem_range.mp hi
  have hji : j < i := Finset.mem_range.mp hj
  have hjn : j < n := lt_trans hji hin
  have hcd : (⟨i, hin⟩ : Fin n) ≠ ⟨j, hjn⟩ := by
    intro h
    have hv : i = j := by
      simpa only [Fin.val_mk] using congrArg Fin.val h
    omega
  have hlocal :=
    crossTranslatedLossSlice_inter_card_le_sum_min_dyadic
      C exponent hexp honeLoss choice hcd
  simpa [lossSliceAtNat, lossPairwiseActualEdgeDyadicCostAtNat,
    hin, hjn] using hlocal

#print axioms translatedLossDuplicateDebt_le_actualEdge_dyadic_pairBudget

end OrderedEdgeColoring
end JSP000404Research
