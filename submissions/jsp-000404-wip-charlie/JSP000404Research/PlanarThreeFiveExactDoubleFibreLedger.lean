import JSP000404Research.ResidualLossCollisionSharedCornerHallObstruction
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

/-- Exact source-native double-hit ledger for n=3 with up to FIVE
actual projected-loss centres, irrespective of the ambient number of
original vertices. The number of loss vertices, rather than all
vertices, is the only structural capacity assumption. -/
theorem actual_three_five_loss_sparsity_duplicate_debt_exact
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hloss : (projectedLossVertices C exponent).card ≤ 5) :
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
      actual_three_colour_five_loss_centre_no_triple_loss_fibre
        C exponent choice hexp hloss q
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

theorem actual_three_five_duplicate_debt_eq_candidates_plus_double_hits
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hfive : Fintype.card V ≤ 5) :
    translatedLossDuplicateDebt C exponent choice =
      (actualLossEarliestOppositeCandidateWords C exponent choice).card +
        (actualLossDoubleHitCandidateWords C exponent choice).card := by
  have hloss : (projectedLossVertices C exponent).card ≤ 5 := by
    have hbound := Finset.card_le_univ (projectedLossVertices C exponent)
    omega
  exact actual_three_five_loss_sparsity_duplicate_debt_exact
    C exponent choice hexp hloss

#print axioms actual_three_five_loss_sparsity_duplicate_debt_exact

/-- The original reuse defect is exactly the actual number of double-hit
targets whenever at most five TRUE projected-loss centres exist. -/
theorem actual_three_loss_sparsity_reuse_defect_eq_double_hit_card
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hloss : (projectedLossVertices C exponent).card ≤ 5) :
    translatedLossDuplicateDebt C exponent choice -
        (actualLossEarliestOppositeCandidateWords C exponent choice).card =
      (actualLossDoubleHitCandidateWords C exponent choice).card := by
  have h := actual_three_five_loss_sparsity_duplicate_debt_exact
    C exponent choice hexp hloss
  omega

/-- With at most THREE genuine projected-loss centres in n=3, no
opposite Boolean candidate can be claimed twice. The original
duplicate-debt count therefore equals the number of DISTINCT
source-native opposite candidates, with no hidden repeated debt.
This allows arbitrarily many non-loss ambient centres. -/
theorem actual_three_loss_centres_duplicate_debt_has_no_reuse
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hloss : (projectedLossVertices C exponent).card ≤ 3) :
    translatedLossDuplicateDebt C exponent choice =
      (actualLossEarliestOppositeCandidateWords C exponent choice).card := by
  classical
  have hfive : (projectedLossVertices C exponent).card ≤ 5 := by
    omega
  have hledger := actual_three_five_loss_sparsity_duplicate_debt_exact
    C exponent choice hexp hfive
  have hzero : (actualLossDoubleHitCandidateWords C exponent choice).card = 0 := by
    by_contra hne
    have hpos : 0 < (actualLossDoubleHitCandidateWords C exponent choice).card := by
      omega
    obtain ⟨q,hq⟩ := Finset.card_pos.mp hpos
    have htwo : 2 ≤ (actualLossOppositeCandidateFibre
        C exponent choice q).card := (Finset.mem_filter.mp hq).2
    have hone := actual_three_colour_three_loss_centre_no_double_fibre
      C exponent choice hexp hloss q
    omega
  rw [hzero] at hledger
  omega

#print axioms actual_three_loss_centres_duplicate_debt_has_no_reuse

#print axioms actual_three_loss_sparsity_reuse_defect_eq_double_hit_card

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

/-- Exact global nonlocal payment IFF in the enlarged n=3 regime
with at most five projected-loss centres, regardless of total vertices. -/
theorem actual_three_loss_sparsity_payment_iff_double_hit_nonlocal
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hloss : (projectedLossVertices C exponent).card ≤ 5) :
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
  have hreuse := actual_three_loss_sparsity_reuse_defect_eq_double_hit_card
    C exponent choice hexp hloss
  rw [hreuse] at hiff
  simpa only [Nat.add_assoc] using hiff

#print axioms actual_three_loss_sparsity_payment_iff_double_hit_nonlocal

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
      ((lossLedgerOutsideTranslatedTrueHoles C exponent choice) \
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
      ((lossLedgerOutsideTranslatedTrueHoles C exponent choice) \
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


/-- Exactly two real original source records at a Boolean candidate
FORCE strict canonical opposite-target reuse. Thus they activate
the EXISTING (kernel-certified) obstruction: purely local square holes
cannot pay the full original collision-record debt, regardless of
which eligible collision squares one tries to combine.

This conclusion is about GENUINE original source records and actual
external holes; it makes NO claim that a nonlocal payment exists. -/
theorem actual_three_five_double_hit_forces_local_square_hall_failure
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hfive : Fintype.card V ≤ 5)
    (hdouble :
      0 < (actualLossDoubleHitCandidateWords C exponent choice).card) :
    ¬ (actualEarliestLossCollisionRecords C exponent choice).card ≤
      ((actualEarliestLossCollisionRecords C exponent choice).biUnion
        (fun a =>
          lossCollisionSquareWords 3 a ∩
            lossLedgerOutsideTranslatedTrueHoles C exponent choice)).card := by
  classical
  let S := actualEarliestLossCollisionRecords C exponent choice
  let O := actualLossEarliestOppositeCandidateWords C exponent choice
  let f : (Fin 3 × Fin 3 × (Fin 3 → Bool)) → (Fin 3 → Bool) :=
    fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  have himage : (S.image f).card = O.card := rfl
  have hrecords :
      S.card = translatedLossDuplicateDebt C exponent choice :=
    actual_earliest_collision_records_card_eq_duplicate_debt
      C exponent choice
  have hledger :
      S.card = O.card +
        (actualLossDoubleHitCandidateWords C exponent choice).card :=
    hrecords.trans
      (actual_three_five_duplicate_debt_eq_candidates_plus_double_hits
        C exponent choice hexp hfive)
  have hRepeated :
      ((actualEarliestLossCollisionRecords C exponent choice).image
        (fun a =>
          flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)).card <
        (actualEarliestLossCollisionRecords C exponent choice).card := by
    change (S.image f).card < S.card
    rw [himage, hledger]
    omega
  exact actual_earliest_loss_collision_local_hall_shortfall_of_reused_corner
    C exponent choice hRepeated

/-- An actual double-hit yields strict local Hall failure even with
arbitrarily many ambient vertices, so long as at most five original
projected-loss centres occur. This is an UNCONDITIONAL implication
under the stated original loss-sparsity hypothesis, not a global
existence claim about nonlocal credit. -/
theorem actual_three_loss_sparsity_double_hit_forces_local_hall_failure
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hloss : (projectedLossVertices C exponent).card ≤ 5)
    (hdouble :
      0 < (actualLossDoubleHitCandidateWords C exponent choice).card) :
    ¬ (actualEarliestLossCollisionRecords C exponent choice).card ≤
      ((actualEarliestLossCollisionRecords C exponent choice).biUnion
        (fun a =>
          lossCollisionSquareWords 3 a ∩
            lossLedgerOutsideTranslatedTrueHoles C exponent choice)).card := by
  classical
  let S := actualEarliestLossCollisionRecords C exponent choice
  let O := actualLossEarliestOppositeCandidateWords C exponent choice
  let f : (Fin 3 × Fin 3 × (Fin 3 → Bool)) → (Fin 3 → Bool) :=
    fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  have himage : (S.image f).card = O.card := rfl
  have hrecords :
      S.card = translatedLossDuplicateDebt C exponent choice :=
    actual_earliest_collision_records_card_eq_duplicate_debt
      C exponent choice
  have hledger :
      S.card = O.card +
        (actualLossDoubleHitCandidateWords C exponent choice).card :=
    hrecords.trans
      (actual_three_five_loss_sparsity_duplicate_debt_exact
        C exponent choice hexp hloss)
  have hRepeated :
      ((actualEarliestLossCollisionRecords C exponent choice).image
        (fun a =>
          flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)).card <
        (actualEarliestLossCollisionRecords C exponent choice).card := by
    change (S.image f).card < S.card
    rw [himage, hledger]
    omega
  exact actual_earliest_loss_collision_local_hall_shortfall_of_reused_corner
    C exponent choice hRepeated


#print axioms actual_three_loss_sparsity_double_hit_forces_local_hall_failure

/-- Under genuine loss-vertex sparsity, successful eight-source
payment has the necessary source-native nonlocal-credit budget. -/
theorem actual_three_loss_sparsity_double_hits_le_nonlocal_credit
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hloss : (projectedLossVertices C exponent).card ≤ 5)
    (hpay :
      terminalTwinOtherFiveDebt C exponent +
          ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
            (lossCoveredBlockerTripleWords C)).card +
          translatedLossDuplicateDebt C exponent choice ≤
        (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
          terminalTwinAvailableSurplus C exponent) :
    (actualLossDoubleHitCandidateWords C exponent choice).card ≤
      ((lossLedgerOutsideTranslatedTrueHoles C exponent choice) \
        actualLossEarliestOppositeCandidateWords C exponent choice).card +
        terminalTwinAvailableSurplus C exponent := by
  have h := (actual_three_loss_sparsity_payment_iff_double_hit_nonlocal
    C exponent choice hexp hloss).mp hpay
  omega

#print axioms actual_three_loss_sparsity_double_hits_le_nonlocal_credit

#print axioms actual_three_five_double_hit_forces_local_square_hall_failure

end OrderedEdgeColoring

namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- Genuine planar AngleCap specialization: for exactly three retained
Boolean coordinates and at most five ORIGINAL plane centres, the real
canonical earliest-prior source ledger equals the distinct candidate count
plus the number of ACTUAL double-hit candidate words. No external-hole
credit is assumed or generated. -/
theorem planar_three_five_standard_duplicate_debt_exact_double_hit_ledger
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hfive : Fintype.card V ≤ 5)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let htpos : 0 < t := by rw [ht]; linarith
    let hwidth : t < (3 : ℝ) + 1 := by rw [ht]; linarith
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D 3 (by exact_mod_cast hwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    ∀ (choice : ProjectionOrdered V → Fin 3),
      translatedLossDuplicateDebt B k choice =
        (actualLossEarliestOppositeCandidateWords B k choice).card +
          (actualLossDoubleHitCandidateWords B k choice).card := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by rw [ht]; linarith
  have hwidth : t < (3 : ℝ) + 1 := by rw [ht]; linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (3 + 1) :=
    standardResidualColoring D 3 (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  change ∀ (choice : ProjectionOrdered V → Fin 3),
    translatedLossDuplicateDebt B k choice =
      (actualLossEarliestOppositeCandidateWords B k choice).card +
        (actualLossDoubleHitCandidateWords B k choice).card
  have hdelta1 : delta < 1 := by linarith
  have hk : ∀ i : ProjectionOrdered V, k i ≤ 2 := by
    intro i
    have hi := centreExponent_lt_n
      (cycles i) 3 delta t (by decide : 1 ≤ (3 : ℕ))
      hdelta0 hdelta1 ht
    dsimp only [k]
    omega
  have hsize : Fintype.card (ProjectionOrdered V) ≤ 5 := by
    have heq : Fintype.card (ProjectionOrdered V) = Fintype.card V := by
      let e : ProjectionOrdered V ≃ V :=
        { toFun := ProjectionOrdered.toOriginal
          invFun := ProjectionOrdered.ofOriginal
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact Fintype.card_congr e
    omega
  intro choice
  exact actual_three_five_duplicate_debt_eq_candidates_plus_double_hits
    B k choice hk hsize

#print axioms planar_three_five_standard_duplicate_debt_exact_double_hit_ledger

end ProjectionOrdered
end JSP000404Research
