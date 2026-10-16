import JSP000404Research.ResidualTerminalTwinActualEdgeCarrierFrontier
import JSP000404Research.ResidualLossWordMultiplicityCoverSplit
import Mathlib.Tactic

/-!
# Exact six-source terminal payment in true Boolean-word multiplicities

This is an equivalence, not a proof of the open global payment.
The original duplicate debt is replaced EXACTLY by two nonnegative
sum categories: (m(word)-1) for loss words already covered by some
original completion cube, and (m(word)-1) for genuine true holes
INSIDE the translated-loss union.

The available hole resources on the RHS remain ONLY true holes
OUTSIDE the translated union. Neither category of duplicated
words is mislabelled as unreserved capacity or an outside true hole.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The original terminal six-source capacity inequality is
equivalent to paying true word-multiplicity excess, split by
original completion coverage, jointly with the other five debts
and the exact actual-colour covered-blocker union. -/
theorem terminalTwinSixSourcePayment_iff_wordMultiplicity_coverSplit
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
        (Finset.sum (translatedLossCoveredWords C exponent choice)
          (fun word => lossWordMultiplicity C exponent choice word - 1)) +
        (Finset.sum (translatedLossTrueHoleWords C exponent choice)
          (fun word => lossWordMultiplicity C exponent choice word - 1)) ≤
        (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
          terminalTwinAvailableSurplus C exponent) := by
  rw [terminalTwinSixSourcePayment_iff_actual_retainedEdgeCarrierFrontier
    C exponent hexp honeLoss hn]
  constructor
  · rintro ⟨choice, hactive, hpay⟩
    refine ⟨choice, hactive, ?_⟩
    rw [translatedLossDuplicateDebt_eq_word_excess_covered_plus_trueHole
      C exponent choice] at hpay
    simpa only [Nat.add_assoc] using hpay
  · rintro ⟨choice, hactive, hpay⟩
    refine ⟨choice, hactive, ?_⟩
    rw [translatedLossDuplicateDebt_eq_word_excess_covered_plus_trueHole
      C exponent choice]
    simpa only [Nat.add_assoc] using hpay

#print axioms terminalTwinSixSourcePayment_iff_wordMultiplicity_coverSplit

end OrderedEdgeColoring
end JSP000404Research
