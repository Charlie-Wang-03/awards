import JSP000404Research.ResidualTerminalTwinActualEdgeCarrierFrontier
import JSP000404Research.ResidualLossActualEdgeCarrierFrontier
import Mathlib.Tactic

/-!
# A finite weighted-edge sufficient condition for all six terminal debts

The exact actual-edge carrier union is a Boolean-word quantity. Its size
is bounded by the sum of endpoint dyadic min-capacities over actual
source--blocker retained edges whose colour matches the selected flip.

Consequently, a direct numerical weighted-edge inequality is a
SUFFICIENT CONDITION for the original six-source payment. This
condition is generally STRONGER than the exact payment, since different
triple intersections may overlap; no equivalence is claimed.

This is a useful optional geometric/combinatorial proof interface,
but it does not establish the required edge inequality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem terminalTwinSixSourcePayment_of_actualEdgeDyadicBudget
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hn : 1 ≤ n)
    (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (hbudget :
      terminalTwinOtherFiveDebt C exponent +
        (∑ z ∈ chosenLossActualEdgeBlockerTriples C exponent choice,
          min (2 ^ projectedFree C z.1.1)
              (2 ^ projectedFree C z.1.2)) +
        translatedLossDuplicateDebt C exponent choice ≤
        (lossLedgerOutsideTranslatedTrueHoles
          C exponent choice).card +
          terminalTwinAvailableSurplus C exponent) :
    terminalTwinOtherFiveDebt C exponent +
      totalDyadicProfileLoss exponent (projectedFree C) ≤
      (2 ^ n - (coveredCompletionWords C).card) +
        terminalTwinAvailableSurplus C exponent := by
  have hcarrier :=
    translatedLossCovered_card_le_actualEdgeTriple_dyadic
      C exponent hexp honeLoss choice hchoice
  have hpay :
      terminalTwinOtherFiveDebt C exponent +
        ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
          (lossCoveredBlockerTripleWords C)).card +
        translatedLossDuplicateDebt C exponent choice ≤
        (lossLedgerOutsideTranslatedTrueHoles
          C exponent choice).card +
          terminalTwinAvailableSurplus C exponent := by
    rw [← translatedLossCovered_eq_actualEdgeTriple_union
      C exponent hexp honeLoss choice hchoice]
    omega
  exact (terminalTwinSixSourcePayment_iff_actual_retainedEdgeCarrierFrontier
    C exponent hexp honeLoss hn).2
    ⟨choice, hchoice, hpay⟩

#print axioms terminalTwinSixSourcePayment_of_actualEdgeDyadicBudget

end OrderedEdgeColoring
end JSP000404Research
