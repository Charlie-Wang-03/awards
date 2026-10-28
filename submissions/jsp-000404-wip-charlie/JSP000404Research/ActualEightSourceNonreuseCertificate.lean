import JSP000404Research.ActualExternalHoleNonreuseCertificate
import Mathlib.Tactic

/-!
# Eight SOURCE-TAGGED real terminal debt classes, only TWO legal credits

Unlike a three-class aggregate, this is the full decomposition into the
actual six remaining terminal contributors:
  (1) covered soft overlap words,
  (2) outgoing movable hard words,
  (3) reverse strict-descent hard words,
  (4) equal-exponent rigid TWIN dyadic mass,
  (5) ascending mixed-rigid dyadic mass,
  (6) descending mixed-rigid dyadic mass;
PLUS (7) actual selected-edge covered loss blocker words and
(8) cross-coordinate translated-loss duplicate debt.

The three genuinely word-indexed source sets use subtype tokens (not
anonymous counts); the other dyadic/multiplicity masses use finite
unit indices with their exact existing, already-certified definitions.

The TWO available credit classes are precisely actual true holes OUTSIDE
translated losses and the already-reserved-free remainder of profile
surplus. One injection from the full tagged disjoint sum prohibits ANY
double use, including across the six different terminal source classes.

This is ONLY a sufficient geometric matching certificate, not a proof
that AngleCap supplies such a matching in every configuration.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

abbrev actualEightSourceDebtTokens
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
    (Fin (translatedLossDuplicateDebt B k choice))))))))

/-- Strictly adequate source-tagged payment interface; all original
terms and their source classes are retained literally. -/
theorem actual_eight_source_injective_payment_suffices
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n)
    (allocate :
      actualEightSourceDebtTokens B k choice →
        actualExternalPaymentCredits B k choice)
    (hinj : Function.Injective allocate) :
    terminalTwinOtherFiveDebt B k +
        ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)).card +
        translatedLossDuplicateDebt B k choice ≤
      (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
        terminalTwinAvailableSurplus B k := by
  classical
  have hcard :=
    Fintype.card_le_of_injective allocate hinj
  simpa only [actualEightSourceDebtTokens, actualExternalPaymentCredits,
    terminalTwinOtherFiveDebt, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_coe, Nat.add_assoc] using hcard

#print axioms actual_eight_source_injective_payment_suffices
end OrderedEdgeColoring
end JSP000404Research
