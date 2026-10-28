import JSP000404Research.ResidualLossGlobalNonlocalShortfallLedger
import Mathlib.Tactic

/-!
# Universal source-native nonreusing local payment of actual eighth debt

Every genuine outside-translated TRUE exterior hole in the original
earliest-prior opposite image has at least one REAL original source
collision record. Choose exactly ONE record per such true hole.
The selected source family injects into the existing true hole pool,
even when an arbitrary number of other records share the same opposite
candidate and even when arbitrarily many loss centres are bichromatic.

This removes the <=3-bichromatic-centres hypothesis for the SOURCE-
SELECTED local payment certificate. The unchosen genuine source
records remain full unpaid eighth debt. ALL seven other classes and
the only genuine NONLOCAL true-hole / unreserved-surplus resources
remain unchanged. The original all-width AngleCap implication is
still mathematically OPEN; no axiom or phantom credit is added.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A finite image has a source-preserving, injective SECTION over
ANY selected finite subset of its image. Sources and target credits
remain actual elements, not anonymous Fin-value debt slots. -/
theorem finite_image_has_source_native_nonreuse_section
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (H : Finset β)
    (hH : H ⊆ S.image f) :
    ∃ T : Finset α,
      T ⊆ S ∧ T.image f = H ∧ Set.InjOn f (T : Set α) := by
  classical
  have hwitness (q : {q : β // q ∈ H}) :
      ∃ a : α, a ∈ S ∧ f a = q.1 := by
    exact Finset.mem_image.mp (hH q.2)
  let sec : {q : β // q ∈ H} → α :=
    fun q => Classical.choose (hwitness q)
  have hsec (q : {q : β // q ∈ H}) :
      sec q ∈ S ∧ f (sec q) = q.1 :=
    Classical.choose_spec (hwitness q)
  let T : Finset α :=
    (Finset.univ : Finset {q : β // q ∈ H}).image sec
  have hsubset : T ⊆ S := by
    intro a ha
    obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp ha
    exact (hsec q).1
  have himage : T.image f = H := by
    ext q
    constructor
    · intro hq
      obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hq
      obtain ⟨z, _hz, haz⟩ := Finset.mem_image.mp ha
      have hqz : q = z.1 := by
        calc
          q = f a := hfa.symm
          _ = f (sec z) := congrArg f haz
          _ = z.1 := (hsec z).2
      rw [hqz]
      exact z.2
    · intro hq
      apply Finset.mem_image.mpr
      refine ⟨sec ⟨q, hq⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr
          ⟨⟨q, hq⟩, Finset.mem_univ _, rfl⟩
      · exact (hsec ⟨q, hq⟩).2
  have hinjOn : Set.InjOn f (T : Set α) := by
    intro a ha b hb hab
    change a ∈ T at ha
    change b ∈ T at hb
    obtain ⟨qa, _hqa, haeq⟩ := Finset.mem_image.mp ha
    obtain ⟨qb, _hqb, hbeq⟩ := Finset.mem_image.mp hb
    have hqeq : qa = qb := by
      apply Subtype.ext
      calc
        qa.1 = f (sec qa) := (hsec qa).2.symm
        _ = f a := congrArg f haeq.symm
        _ = f b := hab
        _ = f (sec qb) := congrArg f hbeq
        _ = qb.1 := (hsec qb).2
    calc
      a = sec qa := haeq.symm
      _ = sec qb := congrArg sec hqeq
      _ = b := hbeq
  exact ⟨T, hsubset, himage, hinjOn⟩

/-- At ALL Boolean widths and for EVERY original residual colouring,
there is an ACTUAL source-native subset of original eighth collision
records whose canonical opposite images are EXACTLY the genuine
locally eligible outside-translated TRUE holes and are ALL distinct.
No original exponent, choice-active or bicolour-count hypothesis. -/
theorem actual_eighth_allwidth_true_local_holes_have_original_section
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    ∃ T : Finset (Fin n × Fin n × (Fin n → Bool)),
      T ⊆ actualEarliestLossCollisionRecords C exponent choice ∧
      T.image (fun a : Fin n × Fin n × (Fin n → Bool) =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1) =
          actualLossEarliestEligibleLocalHoles C exponent choice ∧
      Set.InjOn
        (fun a : Fin n × Fin n × (Fin n → Bool) =>
          flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)
        (T : Set _) := by
  classical
  let S := actualEarliestLossCollisionRecords C exponent choice
  let f : (Fin n × Fin n × (Fin n → Bool)) → (Fin n → Bool) :=
    fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  let H := actualLossEarliestEligibleLocalHoles C exponent choice
  have hH : H ⊆ S.image f := by
    intro q hq
    exact (Finset.mem_inter.mp hq).1
  exact finite_image_has_source_native_nonreuse_section S f H hH

/-- UNIVERSAL exact outstanding payment decomposition for all eight
ORIGINAL debt classes: select ONE real earliest-prior source record for
each genuine local exterior hole, pay it once, and leave the LITERAL
other original source records (including repeated/ineligible targets)
as debts requiring NONLOCAL true holes or genuinely unreserved surplus.

The geometric implication making this residual inequality true is
NOT proved by this equivalence. This is an all-width nonreuse
normal form, not a solution of JSP-000404. -/
theorem actual_eighth_allwidth_payment_iff_unmatched_original_record_count
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    ∃ T : Finset (Fin n × Fin n × (Fin n → Bool)),
      T ⊆ actualEarliestLossCollisionRecords C exponent choice ∧
      T.image (fun a : Fin n × Fin n × (Fin n → Bool) =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1) =
          actualLossEarliestEligibleLocalHoles C exponent choice ∧
      Set.InjOn
        (fun a : Fin n × Fin n × (Fin n → Bool) =>
          flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)
        (T : Set _) ∧
      ((terminalTwinOtherFiveDebt C exponent +
          ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
            (lossCoveredBlockerTripleWords C)).card +
          translatedLossDuplicateDebt C exponent choice ≤
        (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
          terminalTwinAvailableSurplus C exponent) ↔
       (terminalTwinOtherFiveDebt C exponent +
          ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
            (lossCoveredBlockerTripleWords C)).card +
          (actualEarliestLossCollisionRecords C exponent choice \ T).card ≤
        ((lossLedgerOutsideTranslatedTrueHoles C exponent choice) \
          actualLossEarliestOppositeCandidateWords C exponent choice).card +
          terminalTwinAvailableSurplus C exponent)) := by
  classical
  obtain ⟨T, hsub, himage, hinj⟩ :=
    actual_eighth_allwidth_true_local_holes_have_original_section
      C exponent choice
  refine ⟨T, hsub, himage, hinj, ?_⟩
  let S := actualEarliestLossCollisionRecords C exponent choice
  let O := actualLossEarliestOppositeCandidateWords C exponent choice
  let Q := lossLedgerOutsideTranslatedTrueHoles C exponent choice
  have hcardsection : T.card = (Q ∩ O).card := by
    calc
      T.card = (T.image (fun a : Fin n × Fin n × (Fin n → Bool) =>
          flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ = (actualLossEarliestEligibleLocalHoles C exponent choice).card :=
        congrArg Finset.card himage
      _ = (Q ∩ O).card := by rw [Finset.inter_comm]
  have hsplit : (S \ T).card + T.card = S.card := by
    have h := Finset.card_sdiff_add_card_inter S T
    rw [Finset.inter_eq_right.mpr hsub] at h
    exact h
  have hholes := Finset.card_sdiff_add_card_inter Q O
  have hsource : translatedLossDuplicateDebt C exponent choice = S.card :=
    (actual_earliest_collision_records_card_eq_duplicate_debt
      C exponent choice).symm
  change
    (terminalTwinOtherFiveDebt C exponent +
      ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
        (lossCoveredBlockerTripleWords C)).card +
      translatedLossDuplicateDebt C exponent choice ≤
      Q.card + terminalTwinAvailableSurplus C exponent) ↔
    (terminalTwinOtherFiveDebt C exponent +
      ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
        (lossCoveredBlockerTripleWords C)).card +
      (S \ T).card ≤
      (Q \ O).card + terminalTwinAvailableSurplus C exponent)
  constructor <;> intro h <;> omega

#print axioms finite_image_has_source_native_nonreuse_section
#print axioms actual_eighth_allwidth_true_local_holes_have_original_section
#print axioms actual_eighth_allwidth_payment_iff_unmatched_original_record_count

end OrderedEdgeColoring
end JSP000404Research
