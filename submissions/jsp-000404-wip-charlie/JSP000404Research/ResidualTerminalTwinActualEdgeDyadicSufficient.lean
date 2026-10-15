import JSP000404Research.ResidualLossGlobalDuplicateDyadicBudget
import JSP000404Research.ResidualTerminalTwinActualEdgeCarrierFrontier
import Mathlib.Tactic

/-!
# Sufficient terminal six-source payment with no abstract duplicate debt

This module replaces the global translated-loss duplicate debt in the
already certified terminal actual-edge carrier payment by a concrete,
conservative, computable-in-principle sum over all genuine cross-coordinate
retained-edge collision carriers. The six-source payment is NOT proved:
the displayed new upper budget remains an explicit hypothesis.

In particular, this is not an injection of Boolean words into outside
true holes, not a new supply of surplus, and not a proof of the original
JSP-000404 problem. The admitted WIP sorry remains unmodified.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A numerically explicit sufficient final payment certificate:
the duplicate debt can be eliminated from the HYPOTHESIS and replaced
by the independently proved actual-edge dyadic upper envelope. -/
theorem terminalTwinSixSourcePayment_of_actualEdge_dyadic_pairBudget
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hn : 1 ≤ n)
    (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (hbudget :
      terminalTwinOtherFiveDebt C exponent +
        ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
          (lossCoveredBlockerTripleWords C)).card +
        (∑ i ∈ Finset.range n,
          ∑ j ∈ Finset.range i,
            lossPairwiseActualEdgeDyadicCostAtNat
              C exponent choice i j) ≤
        (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
          terminalTwinAvailableSurplus C exponent) :
    terminalTwinOtherFiveDebt C exponent +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
        (2 ^ n - (coveredCompletionWords C).card) +
          terminalTwinAvailableSurplus C exponent := by
  have hdup :=
    translatedLossDuplicateDebt_le_actualEdge_dyadic_pairBudget
      C exponent hexp honeLoss choice
  have hpay :
      terminalTwinOtherFiveDebt C exponent +
        ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
          (lossCoveredBlockerTripleWords C)).card +
        translatedLossDuplicateDebt C exponent choice ≤
        (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
          terminalTwinAvailableSurplus C exponent := by
    omega
  exact
    (terminalTwinSixSourcePayment_iff_actual_retainedEdgeCarrierFrontier
      C exponent hexp honeLoss hn).2 ⟨choice, hchoice, hpay⟩

#print axioms terminalTwinSixSourcePayment_of_actualEdge_dyadic_pairBudget

end OrderedEdgeColoring
end JSP000404Research
