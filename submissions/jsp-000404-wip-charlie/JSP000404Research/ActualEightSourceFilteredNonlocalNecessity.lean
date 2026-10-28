import JSP000404Research.ActualEarliestBicolourRecordCapacity
import JSP000404Research.ResidualLossGlobalNonlocalShortfallLedger
import Mathlib.Tactic

/-!
# Quantified remaining nonlocal payment necessity from TRUE owner rectangles

The original duplicate-debt count D is exact and source-native.  The
number of ACTUALLY usable eighth-lane LOCAL TRUE holes is at most the
number R of genuine earliest-prior debt records whose original owners
share both collision colours. Consequently, at least D - R units of
the original duplicate debt must be paid NONLOCALLY.  This proof
cancels real local holes exactly once, never invents missing exterior
hole credits, and does not pretend R itself consists of valid holes.

The result is a NECESSARY constraint for any hoped-for full eight-source
payment from AngleCap.  It does not prove that payment inequality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Strong source-native necessary nonlocal resource inequality for
ANY full payment: seven original debts plus the original eighth
duplicate debt that CANNOT even fit into bichromatic-owner records
must be paid exclusively by actual NONLOCAL true exterior holes and
genuinely unreserved surplus. -/
theorem actual_eight_source_payment_requires_bicolour_filtered_nonlocal_credit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices B k,
      choice v ∈ retainedActive B v)
    (hpay :
      terminalTwinOtherFiveDebt B k +
          ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
            (lossCoveredBlockerTripleWords B)).card +
          translatedLossDuplicateDebt B k choice ≤
        (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
          terminalTwinAvailableSurplus B k) :
    terminalTwinOtherFiveDebt B k +
        ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)).card +
        (translatedLossDuplicateDebt B k choice -
          (actualEarliestBicolourRecordCandidates B k choice).card) ≤
      ((lossLedgerOutsideTranslatedTrueHoles B k choice) \
        actualLossEarliestOppositeCandidateWords B k choice).card +
        terminalTwinAvailableSurplus B k := by
  classical
  have hres := (actual_eight_source_payment_iff_nonlocal_defect_payment
    B k choice).mp hpay
  have hsplit :=
    actual_loss_duplicate_debt_eq_local_plus_reuse_ineligible B k choice
  have hcap :=
    actual_earliest_eligible_local_holes_card_le_bicolour_records
      B k choice hchoice
  omega

#print axioms actual_eight_source_payment_requires_bicolour_filtered_nonlocal_credit

end OrderedEdgeColoring
end JSP000404Research
