import JSP000404Research.PlanarThreeFiveLossDuplicateBound
import JSP000404Research.ResidualLossGlobalNonlocalShortfallLedger
import Mathlib.Tactic

/-!
# n=3 five-centre EXACT genuine double-target collision debit

The previous original source-native n=3 five-centre fibre bound says
each real canonical opposite candidate has ONE or TWO debt records.
The excess debit Ddup - |O| is therefore EXACTLY the number of
distinct actual Boolean opposite targets whose true fibre has TWO
source records. There is no abstract surrogate or reused credit.

Substituting this exact integer into the existing eight-source
global nonlocal payment equivalence yields a more explicit residual
frontier: other seven real debts + actual two-hit targets + truly
ineligible opposite candidates must be paid from nonlocal real
outside holes and genuinely unreserved surplus.

These theorems make NO claim that the reduced payment follows from
AngleCap and do not close the last root proof sorry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Real original opposite Boolean candidates claimed TWICE by distinct
canonical earliest-prior projected-loss collision debt records. -/
noncomputable def actualLossDoubleHitCandidateWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    Finset (Fin n → Bool) :=
  (actualLossEarliestOppositeCandidateWords C exponent choice).filter
    (fun q => 2 ≤ (actualLossOppositeCandidateFibre C exponent choice q).card)

/-- Exact original duplicate debt, n=3, five-centre condition:
the first debt record of each distinct opposite candidate costs one;
each double-hit opposite target costs exactly ONE further unit. -/
theorem actual_three_five_duplicate_debt_eq_candidates_plus_double_hits
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hfive : Fintype.card V ≤ 5) :
    translatedLossDuplicateDebt C exponent choice =
      (actualLossEarliestOppositeCandidateWords C exponent choice).card +
        (actualLossDoubleHitCandidateWords C exponent choice).card := by
  classical
  let O := actualLossEarliestOppositeCandidateWords C exponent choice
  let F := actualLossOppositeCandidateFibre C exponent choice
  let D := actualLossDoubleHitCandidateWords C exponent choice
  have hsum := actual_loss_duplicate_debt_eq_sum_opposite_fibre_card
    C exponent choice
  have hpositive (q : Fin 3 → Bool) (hq : q ∈ O) : 1 ≤ (F q).card := by
    obtain ⟨a, ha, hf⟩ := Finset.mem_image.mp hq
    have hm : a ∈ F q :=
      Finset.mem_filter.mpr ⟨ha, hf⟩
    exact Finset.one_le_card.mpr ⟨a, hm⟩
  have hpoint (q : Fin 3 → Bool) (hq : q ∈ O) :
      (F q).card = 1 + if 2 ≤ (F q).card then 1 else 0 := by
    have hlo := hpositive q hq
    have hhi : (F q).card ≤ 2 :=
      actual_three_colour_five_centre_no_triple_loss_fibre
        C exponent choice hexp hfive q
    split_ifs <;> omega
  have hfilter :
      (∑ q ∈ O, if 2 ≤ (F q).card then (1 : ℕ) else 0) = D.card := by
    change (∑ q ∈ O, if 2 ≤ (F q).card then (1 : ℕ) else 0) =
      (O.filter (fun q => 2 ≤ (F q).card)).card
    simp
  have hcount :
      (∑ q ∈ O, (F q).card) = O.card + D.card := by
    calc
      (∑ q ∈ O, (F q).card) =
          ∑ q ∈ O, (1 + if 2 ≤ (F q).card then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro q hq
            exact hpoint q hq
      _ = (∑ q ∈ O, (1 : ℕ)) +
          (∑ q ∈ O, if 2 ≤ (F q).card then (1 : ℕ) else 0) := by
            rw [Finset.sum_add_distrib]
      _ = O.card + D.card := by
        rw [hfilter]
        simp
  dsimp only [O, F, D] at hcount
  omega

/-- The exact original reuse defect is precisely the NUMBER of
ACTUAL double-hit opposite words, without any dummy charge. -/
theorem actual_three_five_reuse_defect_eq_double_hit_card
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hfive : Fintype.card V ≤ 5) :
    translatedLossDuplicateDebt C exponent choice -
        (actualLossEarliestOppositeCandidateWords C exponent choice).card =
      (actualLossDoubleHitCandidateWords C exponent choice).card := by
  have h := actual_three_five_duplicate_debt_eq_candidates_plus_double_hits
    C exponent choice hexp hfive
  omega

/-- Fully source-native five-centre form of the original eight-source
payment: only actual double-hit targets, actual ineligible candidates,
all other original debts, and REAL nonlocal credit resources remain.
This is a LOGICAL IFF and is NOT a sufficiency theorem from AngleCap. -/
theorem actual_three_five_eight_source_payment_iff_double_hit_nonlocal
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hfive : Fintype.card V ≤ 5) :
    (terminalTwinOtherFiveDebt C exponent +
        ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
          (lossCoveredBlockerTripleWords C)).card +
        translatedLossDuplicateDebt C exponent choice ≤
      (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
        terminalTwinAvailableSurplus C exponent) ↔
    (terminalTwinOtherFiveDebt C exponent +
        ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
          (lossCoveredBlockerTripleWords C)).card +
        (actualLossDoubleHitCandidateWords C exponent choice).card +
        ((actualLossEarliestOppositeCandidateWords C exponent choice) \
          lossLedgerOutsideTranslatedTrueHoles C exponent choice).card ≤
      ((lossLedgerOutsideTranslatedTrueHoles C exponent choice) \
        actualLossEarliestOppositeCandidateWords C exponent choice).card +
        terminalTwinAvailableSurplus C exponent) := by
  have hiff := actual_eight_source_payment_iff_nonlocal_defect_payment
    C exponent choice
  have hreuse := actual_three_five_reuse_defect_eq_double_hit_card
    C exponent choice hexp hfive
  rw [hreuse] at hiff
  simpa only [Nat.add_assoc] using hiff

#print axioms actual_three_five_duplicate_debt_eq_candidates_plus_double_hits
#print axioms actual_three_five_reuse_defect_eq_double_hit_card
#print axioms actual_three_five_eight_source_payment_iff_double_hit_nonlocal


/-- Any successful ORIGINAL eight-source payment must be able to cover
EVERY genuine two-hit opposite target by real nonlocal outside holes or
unreserved dyadic surplus. This is a necessary condition, not a construction
of such credit. -/
theorem actual_three_five_double_hits_le_available_nonlocal_credit
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hfive : Fintype.card V ≤ 5)
    (hpay :
      terminalTwinOtherFiveDebt C exponent +
          ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
            (lossCoveredBlockerTripleWords C)).card +
          translatedLossDuplicateDebt C exponent choice ≤
        (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
          terminalTwinAvailableSurplus C exponent) :
    (actualLossDoubleHitCandidateWords C exponent choice).card ≤
      ((lossLedgerOutsideTranslatedTrueHoles C exponent choice) \\
        actualLossEarliestOppositeCandidateWords C exponent choice).card +
        terminalTwinAvailableSurplus C exponent := by
  have h := (actual_three_five_eight_source_payment_iff_double_hit_nonlocal
    C exponent choice hexp hfive).mp hpay
  omega

/-- A source-native, checkable NEGATIVE certificate for the residual
eight-source budget: strictly more original double-hit candidates than
all truly external, nonreused credit already rules out payment.
The theorem does not assume this shortfall always occurs. -/
theorem actual_three_five_payment_impossible_of_double_hit_shortfall
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hfive : Fintype.card V ≤ 5)
    (hshort :
      ((lossLedgerOutsideTranslatedTrueHoles C exponent choice) \\
        actualLossEarliestOppositeCandidateWords C exponent choice).card +
        terminalTwinAvailableSurplus C exponent <
      (actualLossDoubleHitCandidateWords C exponent choice).card) :
    ¬ (terminalTwinOtherFiveDebt C exponent +
          ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
            (lossCoveredBlockerTripleWords C)).card +
          translatedLossDuplicateDebt C exponent choice ≤
        (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
          terminalTwinAvailableSurplus C exponent) := by
  intro hpay
  have hcredit := actual_three_five_double_hits_le_available_nonlocal_credit
    C exponent choice hexp hfive hpay
  omega

#print axioms actual_three_five_double_hits_le_available_nonlocal_credit
#print axioms actual_three_five_payment_impossible_of_double_hit_shortfall

end OrderedEdgeColoring
end JSP000404Research
