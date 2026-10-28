import JSP000404Research.ResidualLossCanonicalRecordDebtEquiv
import JSP000404Research.ResidualLossTwoColourOppositeNoReuse
import JSP000404Research.ActualEightSourceEarliestDebtPayment
import Mathlib.Tactic

/-!
# Exact original eight-source global payment after cancelling ACTUAL local holes

An earliest-prior source unit is not automatically paid by its opposite
double-flip target. The true usable square-local hole set is exactly
  O ∩ Q
where O is the image of the original source-native opposite map, and
Q is the genuine global outside-translated true-hole pool.

The original projected-loss duplicate debt splits WITHOUT inequalities:
  Ddup = |O ∩ Q| + (Ddup - |O|) + |O \ Q|.
The two remaining defects are:
  * genuine repeated opposite targets, and
  * distinct opposite candidates which are NOT eligible true holes.
The global true-hole pool splits as
  |Q| = |O ∩ Q| + |Q \ O|.
We cancel ONLY the SAME real holes on both sides of the original
NUMERICAL eight-source payment frontier. No injection, or any credit,
is manufactured. This is an EQUIVALENT exact residual condition,
NOT a proof that the residual condition follows from AngleCap.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Image of the exact earliest-prior original duplicate-debt records
under their canonical opposite double-flip candidate word map. -/
noncomputable def actualLossEarliestOppositeCandidateWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    Finset (Fin n → Bool) :=
  (actualEarliestLossCollisionRecords C exponent choice).image
    (fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)

/-- Only ACTUAL exterior true holes in the original collision
squares are algebraically eligible for local cancellation. -/
noncomputable def actualLossEarliestEligibleLocalHoles
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    Finset (Fin n → Bool) :=
  actualLossEarliestOppositeCandidateWords C exponent choice ∩
    lossLedgerOutsideTranslatedTrueHoles C exponent choice

/-- Every square-local TRUE hole from the actual original duplicate-debt
records is precisely one genuine eligible opposite candidate.
This is set equality, not just an upper bound. -/
theorem actual_earliest_local_holes_eq_eligible_candidates
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    (actualEarliestLossCollisionRecords C exponent choice).biUnion
      (fun a =>
        lossCollisionSquareWords n a ∩
          lossLedgerOutsideTranslatedTrueHoles C exponent choice) =
      actualLossEarliestEligibleLocalHoles C exponent choice := by
  exact actual_earliest_loss_collision_local_holes_exact_image_inter
    C exponent choice

/-- EXACT original duplicate-debt decomposition: each genuine local
true-hole credit is counted ONCE, and the remaining liability is
partitioned into (i) repeated candidates and (ii) ineligible candidates.
Both nonnegative components are source-native; no arbitrary Hall
condition or planar hypothesis enters the accounting. -/
theorem actual_loss_duplicate_debt_eq_local_plus_reuse_ineligible
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    translatedLossDuplicateDebt C exponent choice =
      (actualLossEarliestEligibleLocalHoles C exponent choice).card +
      ((translatedLossDuplicateDebt C exponent choice -
          (actualLossEarliestOppositeCandidateWords C exponent choice).card) +
        ((actualLossEarliestOppositeCandidateWords C exponent choice) \
          lossLedgerOutsideTranslatedTrueHoles C exponent choice).card) := by
  classical
  let S := actualEarliestLossCollisionRecords C exponent choice
  let O := actualLossEarliestOppositeCandidateWords C exponent choice
  let Q := lossLedgerOutsideTranslatedTrueHoles C exponent choice
  change translatedLossDuplicateDebt C exponent choice =
    (O ∩ Q).card +
      ((translatedLossDuplicateDebt C exponent choice - O.card) +
        (O \ Q).card)
  have hle : O.card ≤ translatedLossDuplicateDebt C exponent choice := by
    calc
      O.card ≤ S.card := Finset.card_image_le
      _ = translatedLossDuplicateDebt C exponent choice :=
        actual_earliest_collision_records_card_eq_duplicate_debt
          C exponent choice
  have hpart := Finset.card_sdiff_add_card_inter O Q
  omega

/-- An equivalent and MORE TARGETED form of the original exact EIGHT-
SOURCE numerical payment obligation. After cancelling the original
genuine local collision holes, the remaining seven-source debt plus
real opposite-image reuse and ineligible-candidate defect must be
paid by ONLY NONLOCAL true holes and genuinely unreserved surplus.

All types of credit remain source-native. This does NOT construct
the required payment or show it follows from AngleCap. -/
theorem actual_eight_source_payment_iff_nonlocal_defect_payment
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n) :
    (terminalTwinOtherFiveDebt B k +
        ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)).card +
        translatedLossDuplicateDebt B k choice ≤
      (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
        terminalTwinAvailableSurplus B k) ↔
    (terminalTwinOtherFiveDebt B k +
        ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)).card +
        ((translatedLossDuplicateDebt B k choice -
            (actualLossEarliestOppositeCandidateWords B k choice).card) +
          ((actualLossEarliestOppositeCandidateWords B k choice) \
            lossLedgerOutsideTranslatedTrueHoles B k choice).card) ≤
      ((lossLedgerOutsideTranslatedTrueHoles B k choice) \
        actualLossEarliestOppositeCandidateWords B k choice).card +
        terminalTwinAvailableSurplus B k) := by
  classical
  let O := actualLossEarliestOppositeCandidateWords B k choice
  let Q := lossLedgerOutsideTranslatedTrueHoles B k choice
  have hdup :=
    actual_loss_duplicate_debt_eq_local_plus_reuse_ineligible
      B k choice
  change translatedLossDuplicateDebt B k choice =
      (O ∩ Q).card +
      ((translatedLossDuplicateDebt B k choice - O.card) +
        (O \ Q).card) at hdup
  have hholes := Finset.card_sdiff_add_card_inter Q O
  have hcomm : (O ∩ Q).card = (Q ∩ O).card := by
    rw [Finset.inter_comm]
  dsimp only [O, Q] at hdup hholes hcomm
  omega

/-- In TWO colours the candidate-reuse part is unconditionally zero,
so the entire original payment frontier is equivalent to the
seven-source liability PLUS precisely the number of INELIGIBLE
distinct candidate opposite words, paid only by truly NONLOCAL
outside holes or surplus. Eligibility is NOT assumed or proved. -/
theorem actual_two_colour_eight_source_payment_iff_nonlocal_ineligibility
    {V : Type*} [LinearOrder V] [Fintype V]
    (B : OrderedEdgeColoring V (2 + 1))
    (k : V → ℕ) (choice : V → Fin 2) :
    (terminalTwinOtherFiveDebt B k +
        ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)).card +
        translatedLossDuplicateDebt B k choice ≤
      (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
        terminalTwinAvailableSurplus B k) ↔
    (terminalTwinOtherFiveDebt B k +
        ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)).card +
        ((actualLossEarliestOppositeCandidateWords B k choice) \
          lossLedgerOutsideTranslatedTrueHoles B k choice).card ≤
      ((lossLedgerOutsideTranslatedTrueHoles B k choice) \
        actualLossEarliestOppositeCandidateWords B k choice).card +
        terminalTwinAvailableSurplus B k) := by
  classical
  have hcard :
      (actualLossEarliestOppositeCandidateWords B k choice).card =
        translatedLossDuplicateDebt B k choice :=
    actual_two_colour_earliest_loss_opposite_image_card_eq_debt B k choice
  have hmain := actual_eight_source_payment_iff_nonlocal_defect_payment
    B k choice
  simpa only [hcard, Nat.sub_self, zero_add] using hmain

#print axioms actual_earliest_local_holes_eq_eligible_candidates
#print axioms actual_loss_duplicate_debt_eq_local_plus_reuse_ineligible
#print axioms actual_eight_source_payment_iff_nonlocal_defect_payment
#print axioms actual_two_colour_eight_source_payment_iff_nonlocal_ineligibility

end OrderedEdgeColoring
end JSP000404Research
