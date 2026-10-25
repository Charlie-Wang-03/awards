import JSP000404Research.ResidualLossTripleCornerTrueHoleCeiling
import JSP000404Research.ResidualLossGlobalNonlocalShortfallLedger
import Mathlib.Tactic

/-!
# Genuine three-source fibre => GLOBAL hole and nonlocal-payment barriers

Previous certified theorem: when all THREE first-occurrence coordinate
pairs (1,0),(2,0),(2,1) at n=3 target the SAME opposite candidate q,
the entire TRUE exterior hole pool Q is contained in {q, not q}.
Here the ACTUAL canonical source fibre size >=3 is the ONLY source
hypothesis: it automatically implies all three exact membership tests.

Because q itself belongs to O, the globally NONLOCAL real hole set
Q \ O contains at most the antipode. Also Ddup >=3, so the original
NUMERICAL eight-source payment condition forces
  genuinely unreserved surplus >= other seven debts + 1.
In particular any zero-surplus instance with a triple fibre cannot
satisfy the eight-source payment inequality. This is a necessary
obstruction and NOT a proof of the global inequality from AngleCap.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A size-three ACTUAL earliest-prior fibre necessarily exhausts
ALL three legal strict ordered pairs. This is NOT an abstract
three-record assumption; exact source membership is recovered from
the previously certified fibre/inverse-word equivalence. -/
theorem actual_three_colour_triple_fibre_all_source_tests
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (q : Fin 3 → Bool)
    (hthree : 3 ≤ (actualLossOppositeCandidateFibre
      C exponent choice q).card) :
    (flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (1 : Fin 3) ∈
      lossEarliestPairWords (lossSliceAtNat C exponent choice) 1 0) ∧
    (flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (2 : Fin 3) ∈
      lossEarliestPairWords (lossSliceAtNat C exponent choice) 2 0) ∧
    (flipBoolWordAt (flipBoolWordAt q (1 : Fin 3)) (2 : Fin 3) ∈
      lossEarliestPairWords (lossSliceAtNat C exponent choice) 2 1) := by
  classical
  let P := actualLossOppositeEligibleSourcePairs C exponent choice q
  have hEq := actual_loss_opposite_candidate_fibre_card_eq_exact_source_pairs
    C exponent choice q
  have hBound := actual_three_colour_opposite_candidate_fibre_card_le_three
    C exponent choice q
  have hPc : P.card = 3 := by
    dsimp only [P]
    omega
  have hPsub : P ⊆ actualLossOrderedCoordinatePairs 3 := by
    exact Finset.filter_subset _ _
  have hPall : P = actualLossOrderedCoordinatePairs 3 :=
    Finset.eq_of_subset_of_card_le hPsub (by
      rw [actual_three_colour_ordered_pairs_card]
      omega)
  have h10pair : ((1 : Fin 3),(0 : Fin 3)) ∈ P := by
    rw [hPall]
    simp [actualLossOrderedCoordinatePairs]
  have h20pair : ((2 : Fin 3),(0 : Fin 3)) ∈ P := by
    rw [hPall]
    simp [actualLossOrderedCoordinatePairs]
  have h21pair : ((2 : Fin 3),(1 : Fin 3)) ∈ P := by
    rw [hPall]
    simp [actualLossOrderedCoordinatePairs]
  exact ⟨(Finset.mem_filter.mp h10pair).2,
    (Finset.mem_filter.mp h20pair).2,
    (Finset.mem_filter.mp h21pair).2⟩

/-- A triple ACTUAL original duplicate-debt fibre leaves at most TWO
true exterior holes across the ENTIRE n=3 Boolean universe. -/
theorem actual_three_colour_triple_fibre_true_holes_card_le_two
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (q : Fin 3 → Bool)
    (hthree : 3 ≤ (actualLossOppositeCandidateFibre
      C exponent choice q).card) :
    (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card ≤ 2 := by
  rcases actual_three_colour_triple_fibre_all_source_tests
    C exponent choice q hthree with ⟨h10,h20,h21⟩
  exact actual_three_colour_triple_collision_true_holes_card_le_two
    C exponent choice q h10 h20 h21

/-- Since the triple fibre's own opposite target q already belongs
to the actual candidate set O, at most ONE real TRUE exterior hole
remains in the global NONLOCAL pool Q \ O. This is precisely the
supply term in the certified exact residual eight-source payment
equivalence, not a new approximate resource definition. -/
theorem actual_three_colour_triple_fibre_nonlocal_true_holes_card_le_one
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (q : Fin 3 → Bool)
    (hthree : 3 ≤ (actualLossOppositeCandidateFibre
      C exponent choice q).card) :
    ((lossLedgerOutsideTranslatedTrueHoles C exponent choice) \
      actualLossEarliestOppositeCandidateWords C exponent choice).card ≤ 1 := by
  classical
  rcases actual_three_colour_triple_fibre_all_source_tests
    C exponent choice q hthree with ⟨h10,h20,h21⟩
  have hQsub :=
    actual_three_colour_triple_collision_all_true_holes_subset_pair
      C exponent choice q h10 h20 h21
  have hqO : q ∈ actualLossEarliestOppositeCandidateWords C exponent choice := by
    have hpos : 0 < (actualLossOppositeCandidateFibre
        C exponent choice q).card := by omega
    obtain ⟨a,ha⟩ := Finset.card_pos.mp hpos
    have hm := Finset.mem_filter.mp ha
    exact Finset.mem_image.mpr ⟨a, hm.1, hm.2⟩
  have hsub :
      (lossLedgerOutsideTranslatedTrueHoles C exponent choice \
        actualLossEarliestOppositeCandidateWords C exponent choice) ⊆
      ({(fun i => !(q i))} : Finset (Fin 3 → Bool)) := by
    intro r hr
    obtain ⟨hrQ,hrNotO⟩ := Finset.mem_sdiff.mp hr
    have hrPair := Finset.mem_insert.mp (hQsub hrQ)
    rcases hrPair with heq | hanti
    · subst r
      exact False.elim (hrNotO hqO)
    · exact hanti
  exact (Finset.card_le_card hsub).trans (by simp)

/-- NEW original resource obstruction: if a genuine n=3 triple
candidate fibre exists AND the original NUMERICAL eight-source payment
inequality holds, then genuinely UNRESERVED surplus must exceed the
remaining seven source-tagged debt categories by at least ONE.
The conclusion is NOT an assumed resource; this is a necessary
condition that can be used to exclude impossible geometric patterns. -/
theorem actual_three_colour_triple_fibre_eight_source_payment_forces_surplus
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (q : Fin 3 → Bool)
    (hthree : 3 ≤ (actualLossOppositeCandidateFibre
      C exponent choice q).card)
    (hpayment :
      terminalTwinOtherFiveDebt C exponent +
        ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
          (lossCoveredBlockerTripleWords C)).card +
        translatedLossDuplicateDebt C exponent choice ≤
      (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
        terminalTwinAvailableSurplus C exponent) :
    terminalTwinOtherFiveDebt C exponent +
        ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
          (lossCoveredBlockerTripleWords C)).card + 1 ≤
      terminalTwinAvailableSurplus C exponent := by
  classical
  have hQ := actual_three_colour_triple_fibre_true_holes_card_le_two
    C exponent choice q hthree
  have hDebt : 3 ≤ translatedLossDuplicateDebt C exponent choice := by
    have hsub : actualLossOppositeCandidateFibre C exponent choice q ⊆
        actualEarliestLossCollisionRecords C exponent choice :=
      Finset.filter_subset _ _
    calc
      3 ≤ (actualLossOppositeCandidateFibre C exponent choice q).card := hthree
      _ ≤ (actualEarliestLossCollisionRecords C exponent choice).card :=
        Finset.card_le_card hsub
      _ = translatedLossDuplicateDebt C exponent choice :=
        actual_earliest_collision_records_card_eq_duplicate_debt
          C exponent choice
  omega

#print axioms actual_three_colour_triple_fibre_all_source_tests
#print axioms actual_three_colour_triple_fibre_true_holes_card_le_two
#print axioms actual_three_colour_triple_fibre_nonlocal_true_holes_card_le_one
#print axioms actual_three_colour_triple_fibre_eight_source_payment_forces_surplus

end OrderedEdgeColoring
end JSP000404Research
