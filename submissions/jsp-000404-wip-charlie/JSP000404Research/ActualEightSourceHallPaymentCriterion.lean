import JSP000404Research.ActualEightSourceNonreuseCertificate
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Tactic

/-!
# Actual eight-source geometric payment reduced to a FINITE HALL CONDITION

For every unit of the six genuine terminal debt classes, covered actual
blocker words and cross-coordinate duplicate debt, geometry may provide
a finite set of ALLOWED payment credits. The credits are typed:
 * TRUE Boolean holes outside all translated projected-loss slices, OR
 * pre-deducted genuinely available surplus indices.

Hall's marriage theorem turns the family of ALL finite-subset
neighbourhood-capacity inequalities into one nonreusing injection.

This gives a clear, genuinely geometric next proof target. It does NOT
claim the Hall condition holds automatically under AngleCap: that
existence/expansion theorem remains the one global mathematical gap.
-/
namespace JSP000404Research
namespace OrderedEdgeColoring

/-- If every finite set of true debt units has at least as many distinct
eligible genuine resource tokens, then the exact ACTUAL external-hole
payment inequality follows, with NO repeated credits. -/
theorem actual_eight_source_hall_condition_implies_payment
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n)
    (eligible :
      actualEightSourceDebtTokens B k choice →
        Finset (actualExternalPaymentCredits B k choice))
    (hHall :
      ∀ S : Finset (actualEightSourceDebtTokens B k choice),
        S.card ≤ (S.biUnion eligible).card) :
    terminalTwinOtherFiveDebt B k +
        ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)).card +
        translatedLossDuplicateDebt B k choice ≤
      (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
        terminalTwinAvailableSurplus B k := by
  classical
  obtain ⟨allocation, hinjective, _hreal⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective eligible).mp hHall
  exact actual_eight_source_injective_payment_suffices
    B k choice allocation hinjective

#print axioms actual_eight_source_hall_condition_implies_payment
end OrderedEdgeColoring
end JSP000404Research
