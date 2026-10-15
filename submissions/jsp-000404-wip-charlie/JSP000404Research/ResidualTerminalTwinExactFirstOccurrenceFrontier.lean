import JSP000404Research.ResidualLossPairwiseOvercount
import JSP000404Research.ResidualTerminalTwinActualEdgeCarrierFrontier
import Mathlib.Tactic

/-!
# Exact non-conservative first-occurrence duplicate-loss frontier

Unlike the conservative dyadic SUFFICIENT certificate, this statement
is an IFF reformulation of the original terminal six-source payment.
The global duplicate debt is replaced by exactly the true set of
each new slice's previously occupied Boolean words.

This formula is exact, but paying those collision masses jointly with
other debts into genuine holes or unreserved surplus remains unproved.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Completely equivalent terminal debt payment with the actual
cross-coordinate duplicate mass expanded into its exact
first-occurrence finite Boolean overlap ledger. No hole or surplus
claim is added. -/
theorem terminalTwinSixSourcePayment_iff_actualEdge_firstOccurrenceFrontier
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
          (lossSliceAtNat C exponent choice i ∩
            lossPrefixUnion (lossSliceAtNat C exponent choice) i).card) ≤
        (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
          terminalTwinAvailableSurplus C exponent) := by
  rw [terminalTwinSixSourcePayment_iff_actual_retainedEdgeCarrierFrontier
    C exponent hexp honeLoss hn]
  constructor
  · rintro ⟨choice, hactive, hpay⟩
    refine ⟨choice, hactive, ?_⟩
    rw [← translatedLossDuplicateDebt_eq_sum_prior_coordinate_overlaps
      C exponent choice]
    exact hpay
  · rintro ⟨choice, hactive, hpay⟩
    refine ⟨choice, hactive, ?_⟩
    rw [translatedLossDuplicateDebt_eq_sum_prior_coordinate_overlaps
      C exponent choice]
    exact hpay

#print axioms terminalTwinSixSourcePayment_iff_actualEdge_firstOccurrenceFrontier

end OrderedEdgeColoring
end JSP000404Research
