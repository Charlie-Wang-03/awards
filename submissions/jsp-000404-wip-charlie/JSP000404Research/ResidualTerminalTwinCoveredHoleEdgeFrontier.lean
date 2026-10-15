import JSP000404Research.ResidualLossEarliestEdgeCoveredSplit
import JSP000404Research.ResidualTerminalTwinActualEdgeCarrierFrontier
import Mathlib.Tactic

/-!
# The exact terminal six-source frontier split by THIRD-PARTY coverage

The original six-source inequality is equivalent to the existence of
a retained-active flip selection satisfying the external true-hole
payment for three explicit debt components:
1. the other five genuine terminal debts;
2. actual covered same-colour loss-blocker words;
3. exact cross-loss edge collision events, split into words covered by
   SOME original cube (necessarily a third-party cube for active choices)
   and words globally uncovered but still inside translated-loss U.

No double counting is silently dropped and no new true-hole or
unreserved-surplus supply is asserted. The right-hand payment remains
OPEN; this is a sorry-free conditional IFF only.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem terminalTwinSixSourcePayment_iff_covered_trueHole_earliestEdgeFrontier
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
        ((∑ i ∈ Finset.range n,
          ∑ j ∈ Finset.range i,
            lossEarliestEdgeCoveredMassAtNat
              C exponent choice i j) +
          (∑ i ∈ Finset.range n,
          ∑ j ∈ Finset.range i,
            lossEarliestEdgeTrueHoleMassAtNat
              C exponent choice i j)) ≤
        (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
          terminalTwinAvailableSurplus C exponent) := by
  rw [terminalTwinSixSourcePayment_iff_actual_retainedEdgeCarrierFrontier
    C exponent hexp honeLoss hn]
  constructor
  · rintro ⟨choice, hactive, hpay⟩
    refine ⟨choice, hactive, ?_⟩
    rw [← translatedLossDuplicateDebt_eq_covered_plus_trueHole_edge_mass
      C exponent hexp honeLoss choice]
    exact hpay
  · rintro ⟨choice, hactive, hpay⟩
    refine ⟨choice, hactive, ?_⟩
    rw [translatedLossDuplicateDebt_eq_covered_plus_trueHole_edge_mass
      C exponent hexp honeLoss choice]
    exact hpay

#print axioms terminalTwinSixSourcePayment_iff_covered_trueHole_earliestEdgeFrontier

end OrderedEdgeColoring
end JSP000404Research
