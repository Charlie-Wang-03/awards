import JSP000404Research.PlanarLowerBranchActualEdgeCarrierFrontier
import Mathlib.Tactic

/-!
# SOURCE-TAGGED, NONREUSING certificate for ACTUAL external-hole payment

This lemma does NOT assert the existence of an allocation in every
AngleCap configuration. It makes the outstanding geometric obligation
precise: a single global injection from *three differently tagged*
classes of actual terminal debts into the disjoint sum of:
  (1) TRUE Boolean holes outside all translated loss words, and
  (2) indexed genuinely available, unreserved dyadic surplus units.

The first source class `terminalTwinOtherFiveDebt` already aggregates
the remaining five terminal contributions from the canonical six-source
ledger; no new unit of unused surplus is manufactured.

The `Sum` tags on BOTH sides prevent a hole token and a surplus token,
or two debt sources, from being conflated. The key geometric problem is
to BUILD the injection under actual AngleCap; only the reduction
from such a certificate to the exact known frontier is proved here.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Distinguishable debt units, with the blocker words kept at their actual
finset locations rather than replaced by anonymous cardinality tokens. -/
abbrev actualExternalPaymentDebts
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ)
    (choice : V → Fin n) : Type _ :=
  Sum (Fin (terminalTwinOtherFiveDebt B k))
    (Sum
      {w : Fin n → Bool //
        w ∈ (chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)}
      (Fin (translatedLossDuplicateDebt B k choice)))

/-- Exhaustive, REAL, outside-translated true-hole tokens and truly
unreserved surplus. An already covered soft/collision word cannot inhabit
the left summand unless it really satisfies the true-hole predicate. -/
abbrev actualExternalPaymentCredits
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ)
    (choice : V → Fin n) : Type _ :=
  Sum
    {w : Fin n → Bool //
      w ∈ lossLedgerOutsideTranslatedTrueHoles B k choice}
    (Fin (terminalTwinAvailableSurplus B k))

/-- A single injective global matching of source-tagged debt units to genuine
credit tokens suffices for the exact outstanding numerical payment.
Constructing it from planar geometry remains OPEN. -/
theorem actual_external_hole_nonreuse_certificate_implies_payment
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ)
    (choice : V → Fin n)
    (allocation :
      actualExternalPaymentDebts B k choice →
        actualExternalPaymentCredits B k choice)
    (hinjective : Function.Injective allocation) :
    terminalTwinOtherFiveDebt B k +
        ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)).card +
        translatedLossDuplicateDebt B k choice ≤
      (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
        terminalTwinAvailableSurplus B k := by
  classical
  have hcard :=
    Fintype.card_le_of_injective allocation hinjective
  simpa only [actualExternalPaymentDebts, actualExternalPaymentCredits,
    Fintype.card_sum, Fintype.card_fin, Fintype.card_coe] using hcard

#print axioms actual_external_hole_nonreuse_certificate_implies_payment

end OrderedEdgeColoring
end JSP000404Research
