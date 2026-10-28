import JSP000404Research.ActualAnyWidthFourLossCentreReuseBarrier
import Mathlib.Tactic

/-!
# Original-source local Hall and global payment frontier with <=3 loss centres

The arbitrary-n FOUR-centre original collision reuse barrier means that
under exponent(v)<=2, at most three genuine original projected-loss owners
leave NO actual opposite-word REUSE. Thus all genuine collision square
subfamilies satisfy local Hall precisely when every genuine candidate
opposite word is a true EXTERIOR Boolean hole.

The GLOBAL eight-source numerical payment condition is equivalent to
the remaining seven-source burden plus truly NONEXTERIOR candidate liability
being covered by nonlocal real exterior holes and unreserved dyadic surplus.
This is an IFF, not an unconditional AngleCap payment proof.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Under the genuine exponent<=2 profile restriction and at most
three actual projected-loss centres, no collision opposite-word reuse
remains. ALL-subfamilies source-local Hall is equivalent to every
actual opposite candidate being a TRUE exterior hole. -/
theorem actual_any_width_three_loss_centres_hall_iff_true_exterior
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hexp : ∀ v, exponent v ≤ 2)
    (hloss : (projectedLossVertices C exponent).card ≤ 3) :
    (∀ T : Finset (Fin n × Fin n × (Fin n → Bool)),
      T ⊆ actualEarliestLossCollisionRecords C exponent choice →
      T.card ≤
        (T.biUnion (fun a =>
          lossCollisionSquareWords n a ∩
            lossLedgerOutsideTranslatedTrueHoles C exponent choice)).card) ↔
    actualLossEarliestOppositeCandidateWords C exponent choice ⊆
      lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
  classical
  have hiff :=
    actual_original_all_subfamilies_local_hall_iff_no_reuse_and_true_exterior
      C exponent choice
  have hinj :=
    actual_any_width_three_loss_centres_opposite_injective
      C exponent choice hexp hloss
  constructor
  · intro h
    exact (hiff.mp h).2
  · intro houtside
    exact hiff.mpr ⟨hinj, houtside⟩

/-- In the three-real-loss-centre regime, the ORIGINAL eight-source
capacity payment has a source-native exact equivalent: seven real
debt classes PLUS the actual outside-hole-ineligible canonical
opposite-candidate liability must be paid by actual untouched exterior
holes and genuinely unreserved dyadic surplus.

The existential choice, AngleCap geometry and resulting INEQUALITY
remain deliberately unproved in this theorem. -/
theorem actual_any_width_three_loss_centres_eight_payment_iff_nonlocal
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hexp : ∀ v, exponent v ≤ 2)
    (hloss : (projectedLossVertices C exponent).card ≤ 3) :
    (terminalTwinOtherFiveDebt C exponent +
        ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
          (lossCoveredBlockerTripleWords C)).card +
        translatedLossDuplicateDebt C exponent choice ≤
      (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
        terminalTwinAvailableSurplus C exponent) ↔
    (terminalTwinOtherFiveDebt C exponent +
        ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
          (lossCoveredBlockerTripleWords C)).card +
        ((actualLossEarliestOppositeCandidateWords C exponent choice) \
          lossLedgerOutsideTranslatedTrueHoles C exponent choice).card ≤
      ((lossLedgerOutsideTranslatedTrueHoles C exponent choice) \
        actualLossEarliestOppositeCandidateWords C exponent choice).card +
        terminalTwinAvailableSurplus C exponent) := by
  have hiff :=
    actual_eight_source_payment_iff_nonlocal_defect_payment C exponent choice
  have hno :=
    actual_any_width_three_loss_centres_duplicate_debt_no_reuse
      C exponent choice hexp hloss
  rw [hno] at hiff ⊢
  simpa only [Nat.sub_self, zero_add, Nat.add_assoc] using hiff

#print axioms actual_any_width_three_loss_centres_hall_iff_true_exterior
#print axioms actual_any_width_three_loss_centres_eight_payment_iff_nonlocal

end OrderedEdgeColoring
end JSP000404Research
