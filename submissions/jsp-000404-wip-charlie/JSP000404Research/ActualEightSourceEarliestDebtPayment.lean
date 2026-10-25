import JSP000404Research.ResidualLossCanonicalDebtTokenCount
import JSP000404Research.ActualEightSourceNonreuseCertificate
import Mathlib.Tactic

/-!
# Genuine source-native eight-class payment without anonymous duplicate tokens

The old global eight-source certificate represents cross-coordinate translated
loss duplicates as Fin (translatedLossDuplicateDebt ...). That has the right
cardinality, but no concrete source coordinate or original Boolean word.

The certified earliest-prior-coordinate decomposition instead provides the
dependent Sigma type actualEarliestLossDebtTokenType. Its cardinal is EXACTLY
the original duplicate debt. We replace only the eighth source summand by
this typed source family; all six genuine terminal classes, original covered
blockers, and the two legally usable credit classes remain unchanged.

An injection of these now source-native eight classes into REAL exterior
Boolean holes or ALREADY unreserved surplus implies the ACTUAL global
payment inequality. Constructing such an injection from AngleCap remains
OPEN. This reduction neither removes the root sorry nor creates resources.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

abbrev actualEightSourceEarliestDebtTokens
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n) : Type _ :=
  Sum ({w : Fin n → Bool // w ∈ softOverlapCompletionWords B})
    (Sum ({w : Fin n → Bool // w ∈ netTransportableHardWords B k})
    (Sum ({w : Fin n → Bool // w ∈ netStrictDescentRigidWords B k})
    (Sum (Fin (∑ q ∈ netTwinRigidCarriers B k, 2 ^ k q.2))
    (Sum (Fin (∑ q ∈ ascendingUnpaidRigidCarriers B k, 2 ^ k q.1))
    (Sum (Fin (∑ q ∈ descendingUnpaidRigidCarriers B k, 2 ^ k q.2))
    (Sum ({w : Fin n → Bool //
      w ∈ (chosenLossActualEdgeBlockerTriples B k choice).biUnion
        (lossCoveredBlockerTripleWords B)})
      (actualEarliestLossDebtTokenType B k choice)))))))

/-- A genuine single nonreused assignment of every original debt source
including exact (later, earliest-prior, word) loss-duplicate tokens pays
the original eight-class numerical debt. No strengthening or omission
of the original geometric obligations. -/
theorem actual_eight_source_earliest_debt_injection_implies_payment
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n)
    (allocate :
      actualEightSourceEarliestDebtTokens B k choice →
        actualExternalPaymentCredits B k choice)
    (hinj : Function.Injective allocate) :
    terminalTwinOtherFiveDebt B k +
        ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)).card +
        translatedLossDuplicateDebt B k choice ≤
      (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
        terminalTwinAvailableSurplus B k := by
  classical
  have hcard := Fintype.card_le_of_injective allocate hinj
  simpa only [actualEightSourceEarliestDebtTokens,
    actualExternalPaymentCredits,
    terminalTwinOtherFiveDebt,
    Fintype.card_sum, Fintype.card_fin, Fintype.card_coe,
    actual_earliest_loss_debt_tokens_card_eq_duplicate_debt,
    Nat.add_assoc] using hcard

#print axioms actual_eight_source_earliest_debt_injection_implies_payment

end OrderedEdgeColoring
end JSP000404Research
