import JSP000404Research.ResidualLossGlobalNonlocalShortfallLedger
import Mathlib.Tactic

/-!
# Original eighth-source nonlocal defect: EXACT disjoint structural split

The previous source-native ledger cancels ONLY true locally eligible holes
and leaves |O \ Q| unpaid, where O is the original earliest-prior
opposite-image candidate set and Q is the genuine exterior TRUE hole
pool, itself disjoint from all translated projected-loss words.

We now partition the outstanding nonlocal ineligibility into TWO
canonical, DISJOINT, REAL word sets:
* O ∩ K: original candidate words covered by any original retained cube;
* (O ∩ U) \ K: original candidate words not covered by any original
  cube but captured by some actual translated projected-loss slice.

Here K = actual covered completion words; U = union of actual
translated-loss slices. The set partition is EXHAUSTIVE, exact in
cardinality, and avoids counting a word covered AND translated twice.

Combined with the existing exact cancellation, this yields an IFF for
the entire eight-class numerical global debt, with two distinct concrete
nonlocal deficit classes. Still NO geometric AngleCap payment is assumed
or proved.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Original opposite-image candidates that are ACTUALLY covered by
an original retained completion cube. They are not real holes. -/
noncomputable def actualEarliestCoveredOppositeDefect
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n) :
    Finset (Fin n → Bool) :=
  actualLossEarliestOppositeCandidateWords C k choice ∩
    coveredCompletionWords C

/-- Original opposite-image candidates which are globally UNcovered
but IN a genuine translated-loss slice; these are true holes but NOT
credits outside translated loss. -/
noncomputable def actualEarliestUncoveredTranslatedOppositeDefect
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n) :
    Finset (Fin n → Bool) :=
  (actualLossEarliestOppositeCandidateWords C k choice ∩
      translatedLossAllCoordinateWords C k choice) \
    coveredCompletionWords C

/-- EXACT original source-native nonlocal candidate defect as a
disjoint union: genuinely COVERED candidates, plus genuinely
UNcovered but translated-loss-captured candidates. Neither class
contains a spendable outside-translated true hole. -/
theorem actual_earliest_nonlocal_defect_eq_covered_union_uncovered_translated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n) :
    (actualLossEarliestOppositeCandidateWords C k choice \
      lossLedgerOutsideTranslatedTrueHoles C k choice) =
      actualEarliestCoveredOppositeDefect C k choice ∪
        actualEarliestUncoveredTranslatedOppositeDefect C k choice := by
  classical
  ext q
  simp only [actualEarliestCoveredOppositeDefect,
    actualEarliestUncoveredTranslatedOppositeDefect,
    lossLedgerOutsideTranslatedTrueHoles,
    lossLedgerGlobalTrueHoles,
    Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter,
    Finset.mem_univ, true_and]
  tauto

/-- A candidate cannot simultaneously belong to the two
subclasses: the translated-only class has ALREADY removed all
covered words. -/
theorem actual_earliest_covered_uncovered_translated_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n) :
    Disjoint (actualEarliestCoveredOppositeDefect C k choice)
      (actualEarliestUncoveredTranslatedOppositeDefect C k choice) := by
  classical
  apply Finset.disjoint_left.mpr
  intro q hc ht
  have hcovered : q ∈ coveredCompletionWords C :=
    (Finset.mem_inter.mp hc).2
  exact (Finset.mem_sdiff.mp ht).2 hcovered

/-- Cardinal debt identity without ANY double charge of an original
opposite candidate that is both covered and in translated loss. -/
theorem actual_earliest_nonlocal_defect_card_eq_exact_two_classes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n) :
    ((actualLossEarliestOppositeCandidateWords C k choice) \
      lossLedgerOutsideTranslatedTrueHoles C k choice).card =
      (actualEarliestCoveredOppositeDefect C k choice).card +
        (actualEarliestUncoveredTranslatedOppositeDefect C k choice).card := by
  rw [actual_earliest_nonlocal_defect_eq_covered_union_uncovered_translated,
    Finset.card_union_of_disjoint
      (actual_earliest_covered_uncovered_translated_disjoint C k choice)]

/-- The ORIGINAL global eight-class numerical payment is equivalent
to paying the seven other genuine classes, repeated opposite targets,
and BOTH DISJOINT REAL nonlocal obstruction classes from ONLY nonlocal
true exterior holes and genuinely unreserved surplus.

The implication from planar AngleCap to this inequality is OPEN.
No collision candidate is credited merely because it was flipped. -/
theorem actual_eight_source_payment_iff_exact_two_nonlocal_defect_classes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n) :
    (terminalTwinOtherFiveDebt C k +
        ((chosenLossActualEdgeBlockerTriples C k choice).biUnion
          (lossCoveredBlockerTripleWords C)).card +
        translatedLossDuplicateDebt C k choice ≤
      (lossLedgerOutsideTranslatedTrueHoles C k choice).card +
        terminalTwinAvailableSurplus C k) ↔
    (terminalTwinOtherFiveDebt C k +
        ((chosenLossActualEdgeBlockerTriples C k choice).biUnion
          (lossCoveredBlockerTripleWords C)).card +
        ((translatedLossDuplicateDebt C k choice -
            (actualLossEarliestOppositeCandidateWords C k choice).card) +
          ((actualEarliestCoveredOppositeDefect C k choice).card +
            (actualEarliestUncoveredTranslatedOppositeDefect C k choice).card)) ≤
      ((lossLedgerOutsideTranslatedTrueHoles C k choice) \
        actualLossEarliestOppositeCandidateWords C k choice).card +
        terminalTwinAvailableSurplus C k) := by
  classical
  have hmain :=
    actual_eight_source_payment_iff_nonlocal_defect_payment C k choice
  have hsplit :=
    actual_earliest_nonlocal_defect_card_eq_exact_two_classes C k choice
  simpa only [hsplit] using hmain

#print axioms actual_earliest_nonlocal_defect_eq_covered_union_uncovered_translated
#print axioms actual_earliest_covered_uncovered_translated_disjoint
#print axioms actual_earliest_nonlocal_defect_card_eq_exact_two_classes
#print axioms actual_eight_source_payment_iff_exact_two_nonlocal_defect_classes

end OrderedEdgeColoring
end JSP000404Research
