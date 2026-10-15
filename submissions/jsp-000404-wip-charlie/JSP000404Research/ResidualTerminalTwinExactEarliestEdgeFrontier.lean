import JSP000404Research.ResidualLossEarliestActualEdgeGlobalLedger
import JSP000404Research.ResidualTerminalTwinActualEdgeCarrierFrontier
import Mathlib.Tactic

/-!
# Terminal six-source payment EXACTLY on first appearance edge carriers

This is a literal IFF reformulation of the original terminal inequality,
not an extra capacity or hole payment assumption. The projected-loss
duplicate debt is represented exactly by actual source/blocker retained
edge carriers, with words counted at the earliest prior coordinate for
each later loss slice. No claim of global nonreuse across OTHER debt
classes is made; the final payment remains the admitted gap.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- EXACT equivalent terminal six-source condition with no
abstract `translatedLossDuplicateDebt` and NO dyadic overestimate.
Every duplicate event is indexed by its later coordinate, earliest
earlier coordinate, and actual edge carrier pair. -/
theorem terminalTwinSixSourcePayment_iff_earliestActualEdgeFrontier
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hn : 1 ≤ n) :
    (terminalTwinOtherFiveDebt C exponent +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
      (2 ^ n - (coveredCompletionWords C).card) +
        terminalTwinAvailableSurplus C exponent) ↔
    ∃ choice : V → Fin n,
      (∀ v ∈ projectedLossVertices C exponent,
        choice v ∈ retainedActive C v) ∧
      (terminalTwinOtherFiveDebt C exponent +
        ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
          (lossCoveredBlockerTripleWords C)).card +
        (∑ i ∈ Finset.range n,
          ∑ j ∈ Finset.range i,
            lossEarliestActualEdgeMassAtNat
              C exponent choice i j) ≤
        (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
          terminalTwinAvailableSurplus C exponent) := by
  rw [terminalTwinSixSourcePayment_iff_actual_retainedEdgeCarrierFrontier
    C exponent hexp honeLoss hn]
  constructor
  · rintro ⟨choice, hactive, hpay⟩
    refine ⟨choice, hactive, ?_⟩
    rw [← translatedLossDuplicateDebt_eq_sum_earliest_actual_edges
      C exponent hexp honeLoss choice]
    exact hpay
  · rintro ⟨choice, hactive, hpay⟩
    refine ⟨choice, hactive, ?_⟩
    rw [translatedLossDuplicateDebt_eq_sum_earliest_actual_edges
      C exponent hexp honeLoss choice]
    exact hpay

#print axioms terminalTwinSixSourcePayment_iff_earliestActualEdgeFrontier

end OrderedEdgeColoring
end JSP000404Research
