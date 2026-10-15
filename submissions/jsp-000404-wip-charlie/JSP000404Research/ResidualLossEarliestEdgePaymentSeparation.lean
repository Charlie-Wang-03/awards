import JSP000404Research.ResidualLossEarliestActualEdgeNonreuse
import JSP000404Research.ResidualLossExternalHoleBudget
import Mathlib.Tactic

/-!
# A necessary separation: collision words are not outside true holes

The source/blocker carriers in the exact earliest-edge duplicate
ledger consist of translated LOSS words. Therefore an actual carrier
word CANNOT itself be a `lossLedgerOutsideTranslatedTrueHoles`
resource. A global payment must move or match debt events to
*other* Boolean words and/or rely on genuinely unreserved surplus.

This is a proved obstruction to self-credit, NOT a claim that the
required global matching exists. No global six-source sorry is closed.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Each exact first-occurrence collision carrier is a SUBSET of
the genuine translated-loss Boolean union. -/
theorem lossEarliestActualEdgeCarrier_subset_translatedLossAll
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (c d : Fin n) (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d) :
    lossEarliestActualEdgeCarrier C exponent choice c d p ⊆
      translatedLossAllCoordinateWords C exponent choice := by
  classical
  intro word hword
  have hearly :=
    lossEarliestActualEdgeCarrier_subset_earliestPair
      C exponent choice c d p hp hword
  have hc :
      word ∈ lossSliceAtNat C exponent choice c.val :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hearly).1).1
  have hreal :
      word ∈ translatedLossSliceWords C exponent choice c := by
    simpa [lossSliceAtNat, c.isLt] using hc
  unfold translatedLossAllCoordinateWords
  exact Finset.mem_biUnion.mpr
    ⟨c, Finset.mem_univ c, hreal⟩

/-- No genuine edge-carried first-occurrence debt word can itself
be a globally uncovered Boolean hole lying OUTSIDE the entire
translated-loss union. -/
theorem lossEarliestActualEdgeCarrier_disjoint_outside_trueHoles
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (c d : Fin n) (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d) :
    Disjoint
      (lossEarliestActualEdgeCarrier C exponent choice c d p)
      (lossLedgerOutsideTranslatedTrueHoles C exponent choice) := by
  classical
  rw [Finset.disjoint_left]
  intro word hw hhole
  have hused :=
    lossEarliestActualEdgeCarrier_subset_translatedLossAll
      C exponent choice c d p hp hw
  exact (Finset.mem_sdiff.mp hhole).2 hused

#print axioms lossEarliestActualEdgeCarrier_subset_translatedLossAll
#print axioms lossEarliestActualEdgeCarrier_disjoint_outside_trueHoles

end OrderedEdgeColoring
end JSP000404Research
