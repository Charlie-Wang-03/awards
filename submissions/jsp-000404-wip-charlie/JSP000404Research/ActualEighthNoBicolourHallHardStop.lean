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


/-- A stronger, directly original-source local obstruction. It is enough
that every genuinely bichromatic loss centre has the SAME selected loss
colour; unlike the earlier hypothesis, TWO or more bichromatic centres
are explicitly allowed. Every actual earliest-prior collision record
then has ZERO spendable true exterior holes in its own square. -/
theorem actual_eighth_constant_biactive_choice_each_square_has_no_exterior
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (hsame : ∀ v u : V,
      v ∈ projectedLossVertices C exponent →
      u ∈ projectedLossVertices C exponent →
      (∃ c d : Fin n, c ≠ d ∧
        c ∈ retainedActive C v ∧ d ∈ retainedActive C v) →
      (∃ c d : Fin n, c ≠ d ∧
        c ∈ retainedActive C u ∧ d ∈ retainedActive C u) →
      choice v = choice u)
    (a : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice) :
    lossCollisionSquareWords n a ∩
      lossLedgerOutsideTranslatedTrueHoles C exponent choice = ∅ := by
  classical
  have hzero :
      actualLossEarliestEligibleLocalHoles C exponent choice = ∅ :=
    actual_eighth_no_local_exterior_of_biactive_choice_constant
      C exponent choice hchoice hsame
  have hwhole :
      (actualEarliestLossCollisionRecords C exponent choice).biUnion
        (fun b => lossCollisionSquareWords n b ∩
          lossLedgerOutsideTranslatedTrueHoles C exponent choice) = ∅ := by
    rw [actual_earliest_local_holes_eq_eligible_candidates]
    exact hzero
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hwholemem : q ∈
      (actualEarliestLossCollisionRecords C exponent choice).biUnion
        (fun b => lossCollisionSquareWords n b ∩
          lossLedgerOutsideTranslatedTrueHoles C exponent choice) :=
    Finset.mem_biUnion.mpr ⟨a, ha, hq⟩
  rw [hwhole] at hwholemem
  simp at hwholemem

/-- A SINGLE genuine original collision record is already an
inclusion-minimal one-credit local Hall deficit in the chosen-colour-
constant regime. This is strictly sharper than merely extracting an
unspecified finite unit deficit from failed whole-family Hall.
It concerns only local exterior square credits, not nonlocal or surplus
resources needed for global eight-source payment. -/
theorem actual_eighth_constant_biactive_choice_singleton_hall_deficit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (hsame : ∀ v u : V,
      v ∈ projectedLossVertices C exponent →
      u ∈ projectedLossVertices C exponent →
      (∃ c d : Fin n, c ≠ d ∧
        c ∈ retainedActive C v ∧ d ∈ retainedActive C v) →
      (∃ c d : Fin n, c ≠ d ∧
        c ∈ retainedActive C u ∧ d ∈ retainedActive C u) →
      choice v = choice u)
    (hnonempty :
      (actualEarliestLossCollisionRecords C exponent choice).Nonempty) :
    ∃ T : Finset (Fin n × Fin n × (Fin n → Bool)),
      T ⊆ actualEarliestLossCollisionRecords C exponent choice ∧
      T.card = 1 ∧
      (T.biUnion (fun b => lossCollisionSquareWords n b ∩
        lossLedgerOutsideTranslatedTrueHoles C exponent choice)).card +
        1 = T.card := by
  classical
  obtain ⟨a, ha⟩ := hnonempty
  have hzero :=
    actual_eighth_constant_biactive_choice_each_square_has_no_exterior
      C exponent choice hchoice hsame a ha
  refine ⟨{a}, ?_, ?_, ?_⟩
  · simp [ha]
  · simp
  · simp only [Finset.singleton_biUnion, hzero]
    simp

#print axioms actual_eighth_constant_biactive_choice_each_square_has_no_exterior
#print axioms actual_eighth_constant_biactive_choice_singleton_hall_deficit


/-- A sharpened original-source TRUE-hole nonreuse gate. For ANY
Boolean width and ANY original exponent data, if at most THREE
projected-loss centres have two different retained-active colours,
the original earliest-prior opposite map cannot send TWO DISTINCT
records to the SAME GENUINE exterior true hole. This follows from
the FOUR-bichromatic-owner theorem; covered or translated candidates
are NOT asserted injective, and the other seven debts remain. -/
theorem actual_eighth_exterior_no_record_reuse_of_biactive_card_le_three
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (hsmall :
      ((projectedLossVertices C exponent).filter (fun v =>
        ∃ c d : Fin n,
          c ≠ d ∧ c ∈ retainedActive C v ∧
            d ∈ retainedActive C v)).card ≤ 3)
    (a b : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hb : b ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hopposite :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 =
        flipBoolWordAt (flipBoolWordAt b.2.2 b.1) b.2.1)
    (hq :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 ∈
        lossLedgerOutsideTranslatedTrueHoles C exponent choice) :
    a = b := by
  by_contra hab
  have hfour :=
    actual_eighth_reused_exterior_forces_four_biactive_loss_centres
      C exponent choice hchoice a b ha hb hab hopposite hq
  omega


/-- The ORIGINAL eighth-debt records whose literal opposite-corner word
is a genuine outside-translated TRUE hole.  This is a source-native
subset of the already-certified earliest-prior collision records,
not an anonymous cardinality proxy or a new credit supply. -/
noncomputable def actualEighthLocallyPayableRecords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    Finset (Fin n × Fin n × (Fin n → Bool)) :=
  (actualEarliestLossCollisionRecords C exponent choice).filter
    (fun a =>
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 ∈
        lossLedgerOutsideTranslatedTrueHoles C exponent choice)

/-- Exactly, not merely by subset inclusion, the opposite images of
locally payable ORIGINAL records are the already defined actual
eligible eighth-lane TRUE exterior holes. -/
theorem actual_eighth_payable_records_image_eq_true_local_holes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    (actualEighthLocallyPayableRecords C exponent choice).image
      (fun a : Fin n × Fin n × (Fin n → Bool) =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1) =
      actualLossEarliestEligibleLocalHoles C exponent choice := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨a, ha, hqeq⟩ := Finset.mem_image.mp hq
    obtain ⟨hrecord, hreal⟩ := Finset.mem_filter.mp ha
    have hcandidate :
        q ∈ actualLossEarliestOppositeCandidateWords C exponent choice := by
      apply Finset.mem_image.mpr
      exact ⟨a, hrecord, hqeq⟩
    have hcredit :
        q ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
      simpa only [hqeq] using hreal
    exact Finset.mem_inter.mpr ⟨hcandidate, hcredit⟩
  · intro hq
    obtain ⟨hcandidate, hcredit⟩ := Finset.mem_inter.mp hq
    change q ∈
      (actualEarliestLossCollisionRecords C exponent choice).image
        (fun a : Fin n × Fin n × (Fin n → Bool) =>
          flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)
        at hcandidate
    obtain ⟨a, ha, hqeq⟩ := Finset.mem_image.mp hcandidate
    apply Finset.mem_image.mpr
    refine ⟨a, ?_, hqeq⟩
    apply Finset.mem_filter.mpr
    refine ⟨ha, ?_⟩
    simpa only [hqeq] using hcredit

/-- With at most THREE bichromatic projected-loss centres, each
genuine exterior eighth candidate has at most ONE original collision
record preimage. Thus the source-native opposite map is injective on
the real locally payable records; covered/nonlocal opposite words
are explicitly excluded from this claim. -/
theorem actual_eighth_payable_records_injOn_of_biactive_card_le_three
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (hsmall :
      ((projectedLossVertices C exponent).filter (fun v =>
        ∃ c d : Fin n, c ≠ d ∧ c ∈ retainedActive C v ∧
          d ∈ retainedActive C v)).card ≤ 3) :
    Set.InjOn
      (fun a : Fin n × Fin n × (Fin n → Bool) =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)
      (actualEighthLocallyPayableRecords C exponent choice : Set _) := by
  classical
  intro a ha b hb heq
  change a ∈ actualEighthLocallyPayableRecords C exponent choice at ha
  change b ∈ actualEighthLocallyPayableRecords C exponent choice at hb
  obtain ⟨haRecord, haCredit⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbRecord, _⟩ := Finset.mem_filter.mp hb
  exact actual_eighth_exterior_no_record_reuse_of_biactive_card_le_three
    C exponent choice hchoice hsmall a b haRecord hbRecord heq haCredit

/-- A genuine full, NONREUSING LOCAL payment for the entire subfamily
of actually payable ORIGINAL eighth-lane collision records: there is
one distinct TRUE exterior hole for each source, not just an upper
bound on the hole count. The other original debts and the unpayable
eighth records remain outside this local certificate. -/
theorem actual_eighth_payable_records_card_eq_real_holes_of_biactive_le_three
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (hsmall :
      ((projectedLossVertices C exponent).filter (fun v =>
        ∃ c d : Fin n, c ≠ d ∧ c ∈ retainedActive C v ∧
          d ∈ retainedActive C v)).card ≤ 3) :
    (actualEighthLocallyPayableRecords C exponent choice).card =
      (actualLossEarliestEligibleLocalHoles C exponent choice).card := by
  classical
  let f : (Fin n × Fin n × (Fin n → Bool)) → (Fin n → Bool) :=
    fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  have hinj : Set.InjOn f
      (actualEighthLocallyPayableRecords C exponent choice : Set _) :=
    actual_eighth_payable_records_injOn_of_biactive_card_le_three
      C exponent choice hchoice hsmall
  calc
    (actualEighthLocallyPayableRecords C exponent choice).card =
        ((actualEighthLocallyPayableRecords C exponent choice).image f).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = (actualLossEarliestEligibleLocalHoles C exponent choice).card := by
      rw [actual_eighth_payable_records_image_eq_true_local_holes]


/-- A SOURCE-TYPED, explicit, nonreusing assignment of every genuinely
locally payable original eighth-debt record into the FIRST (TRUE
external hole) summand of the ACTUAL global credit type. This does
not allocate ANY of the other seven debt classes, nor any source
whose opposite word is covered or translated-loss-captured. -/
theorem actual_eighth_payable_records_have_real_credit_injection_of_biactive_le_three
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (hsmall :
      ((projectedLossVertices C exponent).filter (fun v =>
        ∃ c d : Fin n, c ≠ d ∧ c ∈ retainedActive C v ∧
          d ∈ retainedActive C v)).card ≤ 3) :
    ∃ allocation :
        {a : Fin n × Fin n × (Fin n → Bool) //
          a ∈ actualEighthLocallyPayableRecords C exponent choice} →
          actualExternalPaymentCredits C exponent choice,
      Function.Injective allocation ∧
      ∀ a, ∃ h :
          {q : Fin n → Bool //
            q ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice},
        allocation a = Sum.inl h ∧
        h.1 = flipBoolWordAt (flipBoolWordAt a.1.2.2 a.1.1) a.1.2.1 := by
  classical
  let opp : (Fin n × Fin n × (Fin n → Bool)) → (Fin n → Bool) :=
    fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  let hole (a : {a : Fin n × Fin n × (Fin n → Bool) //
      a ∈ actualEighthLocallyPayableRecords C exponent choice}) :
      {q : Fin n → Bool //
        q ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice} :=
    ⟨opp a.1, (Finset.mem_filter.mp a.2).2⟩
  let allocation (a : {a : Fin n × Fin n × (Fin n → Bool) //
      a ∈ actualEighthLocallyPayableRecords C exponent choice}) :
      actualExternalPaymentCredits C exponent choice :=
    Sum.inl (hole a)
  have hinjOn :=
    actual_eighth_payable_records_injOn_of_biactive_card_le_three
      C exponent choice hchoice hsmall
  refine ⟨allocation, ?_, ?_⟩
  · intro a b heq
    have hsub : hole a = hole b := Sum.inl.inj heq
    have hword : opp a.1 = opp b.1 :=
      congrArg Subtype.val hsub
    exact Subtype.ext (hinjOn a.2 b.2 hword)
  · intro a
    exact ⟨hole a, rfl, rfl⟩

#print axioms actual_eighth_payable_records_have_real_credit_injection_of_biactive_le_three

#print axioms actual_eighth_payable_records_image_eq_true_local_holes
#print axioms actual_eighth_payable_records_injOn_of_biactive_card_le_three
#print axioms actual_eighth_payable_records_card_eq_real_holes_of_biactive_le_three

#print axioms actual_eighth_exterior_no_record_reuse_of_biactive_card_le_three

#print axioms actual_eighth_square_hall_impossible_of_no_bicolour_pair
#print axioms actual_eighth_no_bicolour_global_payment_requires_nonlocal_candidates

end OrderedEdgeColoring
end JSP000404Research
