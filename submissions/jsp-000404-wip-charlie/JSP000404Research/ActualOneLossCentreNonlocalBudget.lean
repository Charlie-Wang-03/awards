import JSP000404Research.PlanarThreeFiveExactDoubleFibreLedger
import Mathlib.Tactic

/-!
# Actual original one-loss-centre elimination of the eighth debt lane

These are unconditional consequences of original earliest-prior collision
geometry for every Boolean dimension and every finite original vertex set.

If at most one original projected-loss centre exists, there is no original
cross-coordinate earliest-prior collision source and NO eighth-lane debt.
The original global numerical payment obligation is then exactly the
seven-remaining-source obligation. No external Boolean hole or unreserved
surplus is postulated or created.

This is a genuine restricted reduction, NOT a proof of the all-configuration
planar AngleCap inequality and NOT a discharge of the admitted global sorry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- With at most one actual projected-loss centre, the *original*
earliest-prior collision source set itself is empty, for arbitrary n. -/
theorem actual_at_most_one_loss_centre_no_source_records
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hloss : (projectedLossVertices C exponent).card ≤ 1) :
    actualEarliestLossCollisionRecords C exponent choice = ∅ := by
  classical
  have hrecords :=
    actual_earliest_collision_records_card_eq_duplicate_debt C exponent choice
  have hzero :=
    actual_original_at_most_one_loss_centre_no_eighth_debt
      C exponent choice hloss
  exact Finset.card_eq_zero.mp (hrecords.trans hzero)

/-- There are consequently no original candidate opposite corners at all.
In particular, exterior-hole eligibility is vacuous in this subcase. -/
theorem actual_at_most_one_loss_centre_no_opposite_candidates
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hloss : (projectedLossVertices C exponent).card ≤ 1) :
    actualLossEarliestOppositeCandidateWords C exponent choice = ∅ := by
  classical
  simp [actualLossEarliestOppositeCandidateWords,
    actual_at_most_one_loss_centre_no_source_records C exponent choice hloss]

/-- A positive actual original eighth-lane debt needs two distinct genuine
projected-loss centres. This is the induction-ready contrapositive barrier. -/
theorem actual_positive_eighth_debt_forces_two_loss_centres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hpositive : 0 < translatedLossDuplicateDebt C exponent choice) :
    2 ≤ (projectedLossVertices C exponent).card := by
  by_contra hnot
  have hloss : (projectedLossVertices C exponent).card ≤ 1 := by omega
  have hzero :=
    actual_original_at_most_one_loss_centre_no_eighth_debt
      C exponent choice hloss
  omega

/-- Exact elimination of the actual eighth debt from the original
eight-source numerical frontier in the one-loss-centre subcase.
This does NOT establish the remaining seven-source inequality. -/
theorem actual_at_most_one_loss_centre_payment_iff_seven_sources
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hloss : (projectedLossVertices C exponent).card ≤ 1) :
    (terminalTwinOtherFiveDebt C exponent +
        ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
          (lossCoveredBlockerTripleWords C)).card +
        translatedLossDuplicateDebt C exponent choice ≤
      (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
        terminalTwinAvailableSurplus C exponent) ↔
    (terminalTwinOtherFiveDebt C exponent +
        ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
          (lossCoveredBlockerTripleWords C)).card ≤
      (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
        terminalTwinAvailableSurplus C exponent) := by
  have hzero :=
    actual_original_at_most_one_loss_centre_no_eighth_debt
      C exponent choice hloss
  simp only [hzero, Nat.add_zero]

#print axioms actual_at_most_one_loss_centre_no_source_records
#print axioms actual_at_most_one_loss_centre_no_opposite_candidates
#print axioms actual_positive_eighth_debt_forces_two_loss_centres
#print axioms actual_at_most_one_loss_centre_payment_iff_seven_sources

end OrderedEdgeColoring
end JSP000404Research
