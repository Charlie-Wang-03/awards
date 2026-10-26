import JSP000404Research.ActualEarliestBicolourNonlocalBarrier
import JSP000404Research.PlanarThreeFiveExactDoubleFibreLedger
import JSP000404Research.ResidualLossGlobalNonlocalShortfallLedger
import Mathlib.Tactic

/-!
# Exact source-native eighth-lane Hall hard stop

When no TWO distinct original projected-loss centres simultaneously
have two different retained active colours, the existing REAL geometry-
free source certificate shows that NO eighth-lane opposite candidate
is a true exterior Boolean hole.

Consequently, if even one original opposite candidate exists, the
ENTIRE original-source square-local Hall payment is IMPOSSIBLE.
This is a rigorous *negative* result about one proposed credit route,
not a counterexample to JSP-000404 or a proof of the global inequality.

Under any independently established full eight-source payment,
all such opposite candidates must instead be paid by strictly
NONLOCAL exterior holes or genuinely unreserved surplus; the other
seven liabilities remain in the ledger, never dropped.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A nonempty original eighth-lane candidate source set and failure
of the two-bicolour-owner condition prevent even the WHOLE-family
real-square Hall inequality. No cardinality or AngleCap hypothesis
is smuggled into this obstruction. -/
theorem actual_eighth_square_hall_impossible_of_no_bicolour_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (hnoPair : ∀ v u : V,
      v ∈ projectedLossVertices C exponent →
      u ∈ projectedLossVertices C exponent →
      v ≠ u →
      (∀ c d : Fin n, c ∈ retainedActive C v →
        d ∈ retainedActive C v → c = d) ∨
      (∀ c d : Fin n, c ∈ retainedActive C u →
        d ∈ retainedActive C u → c = d))
    (hnonempty :
      (actualLossEarliestOppositeCandidateWords C exponent choice).Nonempty) :
    ¬ ((actualEarliestLossCollisionRecords C exponent choice).card ≤
      ((actualEarliestLossCollisionRecords C exponent choice).biUnion
        (fun a =>
          lossCollisionSquareWords n a ∩
            lossLedgerOutsideTranslatedTrueHoles C exponent choice)).card) := by
  intro hhall
  have hcredit :=
    (actual_original_whole_square_local_hall_iff_eighth_no_reuse_and_exterior
      C exponent choice).mp hhall
  obtain ⟨q, hq⟩ := hnonempty
  have houtside :=
    hcredit.2 hq
  exact (actual_eighth_exterior_requires_two_bicolour_loss_centres
    C exponent choice hchoice hnoPair q hq) houtside

/-- If a full global payment has somehow been established, and no two
loss centres are both bicolour, then the literal entire eighth-lane
opposite-candidate family remains in the NONLOCAL payment debt.
This is a conditional necessary inequality, not proof of payment. -/
theorem actual_eighth_no_bicolour_global_payment_requires_nonlocal_candidates
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (hnoPair : ∀ v u : V,
      v ∈ projectedLossVertices C exponent →
      u ∈ projectedLossVertices C exponent →
      v ≠ u →
      (∀ c d : Fin n, c ∈ retainedActive C v →
        d ∈ retainedActive C v → c = d) ∨
      (∀ c d : Fin n, c ∈ retainedActive C u →
        d ∈ retainedActive C u → c = d))
    (hpay :
      terminalTwinOtherFiveDebt C exponent +
          ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
            (lossCoveredBlockerTripleWords C)).card +
          translatedLossDuplicateDebt C exponent choice ≤
        (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
          terminalTwinAvailableSurplus C exponent) :
    terminalTwinOtherFiveDebt C exponent +
        ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
          (lossCoveredBlockerTripleWords C)).card +
        ((translatedLossDuplicateDebt C exponent choice -
          (actualLossEarliestOppositeCandidateWords C exponent choice).card) +
          (actualLossEarliestOppositeCandidateWords C exponent choice).card) ≤
      ((lossLedgerOutsideTranslatedTrueHoles C exponent choice) \
        actualLossEarliestOppositeCandidateWords C exponent choice).card +
        terminalTwinAvailableSurplus C exponent := by
  have hremaining :=
    (actual_eight_source_payment_iff_nonlocal_defect_payment
      C exponent choice).mp hpay
  have hnonlocal :=
    actual_eighth_all_candidates_nonlocal_of_no_bicolour_pair
      C exponent choice hchoice hnoPair
  rw [hnonlocal] at hremaining
  exact hremaining

#print axioms actual_eighth_square_hall_impossible_of_no_bicolour_pair
#print axioms actual_eighth_no_bicolour_global_payment_requires_nonlocal_candidates

end OrderedEdgeColoring
end JSP000404Research
