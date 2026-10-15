import JSP000404Research.ResidualTerminalTwinActiveExternalFrontier
import JSP000404Research.ResidualLossActualEdgeCarrierFrontier
import Mathlib.Tactic

/-!
# Terminal six-source capacity reduced to actual same-colour retained edges

The global payment from the original lower-branch proof is **equivalent** to
the existence of an actually retained-active loss flip choice satisfying

  five-other-debt + |concrete blocker-triple union| + duplicate debt
      <= true holes outside selected translated-loss mass
         + independently unreserved surplus.

The actual-edge blocker-triple union equals the original covered translated-loss
word set, not merely an overcounting sum. Every eligible triple has an ACTUAL
retained edge between its source and blocker with colour equal to the selected
flip coordinate. Thus this equivalence introduces
NO new assumption and NO missing mass. However it does not prove the
remaining inequality; overlaps between different carrier triples remain
an unsolved allocation issue.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem terminalTwinSixSourcePayment_iff_actual_retainedEdgeCarrierFrontier
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
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
        translatedLossDuplicateDebt C exponent choice ≤
        (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
          terminalTwinAvailableSurplus C exponent) := by
  rw [terminalTwinSixSourcePayment_iff_exists_active_externalFrontier
    C exponent hexp honeLoss hn]
  constructor
  · rintro ⟨choice, hactive, hpay⟩
    refine ⟨choice, hactive, ?_⟩
    rw [← translatedLossCovered_eq_actualEdgeTriple_union
      C exponent hexp honeLoss choice hactive]
    exact hpay
  · rintro ⟨choice, hactive, hpay⟩
    refine ⟨choice, hactive, ?_⟩
    rw [translatedLossCovered_eq_actualEdgeTriple_union
      C exponent hexp honeLoss choice hactive]
    exact hpay

#print axioms terminalTwinSixSourcePayment_iff_actual_retainedEdgeCarrierFrontier

end OrderedEdgeColoring
end JSP000404Research
