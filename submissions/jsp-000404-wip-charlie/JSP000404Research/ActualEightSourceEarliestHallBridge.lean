import JSP000404Research.ActualEightSourceEarliestDebtPayment
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Tactic

/-!
# Full ORIGINAL earliest-source Hall reduction (without anonymous debt slots)

The earlier finite Hall theorem works with the cardinal-equivalent but
anonymous Fin-valued eighth summand.  This replacement instead uses the
ACTUAL earliest-prior canonical original source/debt token type.

Every allowed payment credit is a REAL member of the previously defined
exterior true-hole / pre-unreserved surplus sum type.  Hall expansion for
all finite sets of these source-NATIVE obligations gives one injection,
so the exact original eight-source numerical payment follows.

Establishing Hall EXPANSION from the genuine planar AngleCap constraint
is still open: it is not supplied by the argument below.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Exact original source-preserving Hall certificate: enough
nonreusable REAL external payment credits for every finite subset of
actual typed eight-class debt sources implies the EXACT original
numerical payment, including each genuine canonical earliest collision
record, rather than anonymous duplicate-debt indices. -/
theorem actual_eight_source_earliest_hall_implies_global_payment
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n)
    (eligible :
      actualEightSourceEarliestDebtTokens B k choice →
        Finset (actualExternalPaymentCredits B k choice))
    (hHall :
      ∀ S : Finset (actualEightSourceEarliestDebtTokens B k choice),
        S.card ≤ (S.biUnion eligible).card) :
    terminalTwinOtherFiveDebt B k +
        ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)).card +
        translatedLossDuplicateDebt B k choice ≤
      (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
        terminalTwinAvailableSurplus B k := by
  classical
  obtain ⟨allocate, hinjective, _hallowed⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective eligible).mp hHall
  exact actual_eight_source_earliest_debt_injection_implies_payment
    B k choice allocate hinjective

#print axioms actual_eight_source_earliest_hall_implies_global_payment

end OrderedEdgeColoring
end JSP000404Research
