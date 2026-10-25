import JSP000404Research.PlanarThreeFiveExactDoubleFibreLedger
import Mathlib.Tactic

/-!
# Arbitrary-n original loss-square collisions with at most TWO loss centres

A genuine earliest-prior cross-coordinate collision record has two distinct
original loss-source vertices whose fixed chosen coordinates are different.
When the original projected-loss set has at most two elements, EVERY
genuine collision record must use the SAME coordinate pair. The canonical
double-flip opposite map is already proven injective on each fixed pair.

Therefore the original eighth debt lane has NO opposite-target reuse for
arbitrary n when there are <=2 actual projected-loss centres. All-subfamily
square-local Hall then reduces exactly to true exterior eligibility.
No exterior holes, global seven-source credit or AngleCap payment are assumed.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Each actual earliest-prior record uses two distinct original
projected-loss owners with precisely its two chosen coordinates. -/
theorem actual_earliest_record_has_distinct_original_loss_owners
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (a : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice) :
    ∃ v u : V, v ≠ u ∧
      v ∈ projectedLossVertices C exponent ∧
      u ∈ projectedLossVertices C exponent ∧
      choice v = a.1 ∧ choice u = a.2.1 := by
  classical
  obtain ⟨hne, _, hw, hz⟩ :=
    actual_earliest_loss_collision_record_valid C exponent choice a ha
  obtain ⟨v, hvc, _⟩ := Finset.mem_biUnion.mp hw
  obtain ⟨u, huc, _⟩ := Finset.mem_biUnion.mp hz
  have hv := (mem_lossCoordinateSlice C exponent choice a.1 v).mp hvc
  have hu := (mem_lossCoordinateSlice C exponent choice a.2.1 u).mp huc
  refine ⟨v, u, ?_, hv.1, hu.1, hv.2, hu.2⟩
  intro heq
  subst u
  exact hne (hv.2.symm.trans hu.2)

/-- In the two-source regime, every original earliest-prior record
uses one unique strictly ordered original coordinate pair. -/
theorem actual_at_most_two_loss_centres_original_pair_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hloss : (projectedLossVertices C exponent).card ≤ 2)
    (a b : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hb : b ∈ actualEarliestLossCollisionRecords C exponent choice) :
    (a.1, a.2.1) = (b.1, b.2.1) := by
  classical
  let L := projectedLossVertices C exponent
  obtain ⟨va, ua, hneA, hvaL, huaL, hvaC, huaC⟩ :=
    actual_earliest_record_has_distinct_original_loss_owners
      C exponent choice a ha
  obtain ⟨vb, ub, hneB, hvbL, hubL, hvbC, hubC⟩ :=
    actual_earliest_record_has_distinct_original_loss_owners
      C exponent choice b hb
  have hsubset : ({va, ua} : Finset V) ⊆ L := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hvaL
    · exact huaL
  have htwo : ({va, ua} : Finset V).card = 2 := by
    simp [hneA]
  have hL : ({va, ua} : Finset V) = L :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)
  have hvbCases : vb = va ∨ vb = ua := by
    have hh : vb ∈ ({va, ua} : Finset V) := by
      rw [hL]
      exact hvbL
    simpa using hh
  have hubCases : ub = va ∨ ub = ua := by
    have hh : ub ∈ ({va, ua} : Finset V) := by
      rw [hL]
      exact hubL
    simpa using hh
  have haOrd : choice ua < choice va := by
    rw [hvaC, huaC]
    exact (actual_earliest_loss_collision_record_valid
      C exponent choice a ha).2.1
  have hbOrd : choice ub < choice vb := by
    rw [hvbC, hubC]
    exact (actual_earliest_loss_collision_record_valid
      C exponent choice b hb).2.1
  rcases hvbCases with hVB | hVB
  · rcases hubCases with hUB | hUB
    · exact False.elim (hneB (hVB.trans hUB.symm))
    · apply Prod.ext
      · calc
          a.1 = choice va := hvaC.symm
          _ = choice vb := (congrArg choice hVB).symm
          _ = b.1 := hvbC
      · calc
          a.2.1 = choice ua := huaC.symm
          _ = choice ub := (congrArg choice hUB).symm
          _ = b.2.1 := hubC
  · rcases hubCases with hUB | hUB
    · rw [hVB, hUB] at hbOrd
      exact False.elim ((lt_asymm haOrd hbOrd))
    · exact False.elim (hneB (hVB.trans hUB.symm))

/-- The canonical opposite candidate map is injective on all
genuine original earliest-prior records with <=2 loss centres.
This is valid for EVERY Boolean dimension n. -/
theorem actual_at_most_two_loss_centres_opposite_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hloss : (projectedLossVertices C exponent).card ≤ 2) :
    Set.InjOn
      (fun a : Fin n × Fin n × (Fin n → Bool) =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)
      (actualEarliestLossCollisionRecords C exponent choice) := by
  intro a ha b hb heq
  have hpair :=
    actual_at_most_two_loss_centres_original_pair_unique
      C exponent choice hloss a b ha hb
  exact loss_opposite_same_coordinate_pair_injective a b
    (congrArg Prod.fst hpair) (congrArg Prod.snd hpair) heq

/-- Original eighth-lane duplicate debt equals its count of distinct
canonical opposite candidates, with no reuse, in this two-source regime. -/
theorem actual_at_most_two_loss_centres_duplicate_debt_no_reuse
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hloss : (projectedLossVertices C exponent).card ≤ 2) :
    translatedLossDuplicateDebt C exponent choice =
      (actualLossEarliestOppositeCandidateWords C exponent choice).card := by
  classical
  let S := actualEarliestLossCollisionRecords C exponent choice
  let f : (Fin n × Fin n × (Fin n → Bool)) → (Fin n → Bool) :=
    fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  have hinj : Set.InjOn f S :=
    actual_at_most_two_loss_centres_opposite_injective
      C exponent choice hloss
  calc
    translatedLossDuplicateDebt C exponent choice = S.card :=
      (actual_earliest_collision_records_card_eq_duplicate_debt
        C exponent choice).symm
    _ = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ = (actualLossEarliestOppositeCandidateWords
      C exponent choice).card := rfl

/-- For ALL finite subfamilies of original loss-square records, Hall's
condition is exactly the geometric qualification that EVERY opposite
candidate is genuinely exterior, if <=2 actual loss centres exist. -/
theorem actual_at_most_two_loss_centres_all_subfamilies_hall_iff_exterior
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hloss : (projectedLossVertices C exponent).card ≤ 2) :
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
    actual_at_most_two_loss_centres_opposite_injective
      C exponent choice hloss
  constructor
  · intro h
    exact (hiff.mp h).2
  · intro houtside
    exact hiff.mpr ⟨hinj, houtside⟩

/-- Exact cancellation of the real source-local eighth-lane debt:
the remaining global obligation is the genuine seven-source burden
plus NONEXTERIOR candidate liability against NONLOCAL real holes
and unreserved surplus. Neither exterior eligibility nor credit
sufficiency is postulated. -/
theorem actual_at_most_two_loss_centres_payment_iff_nonlocal
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hloss : (projectedLossVertices C exponent).card ≤ 2) :
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
  have hiff := actual_eight_source_payment_iff_nonlocal_defect_payment
    C exponent choice
  have hno :=
    actual_at_most_two_loss_centres_duplicate_debt_no_reuse
      C exponent choice hloss
  rw [hno] at hiff
  simpa only [Nat.sub_self, zero_add, Nat.add_assoc] using hiff

#print axioms actual_earliest_record_has_distinct_original_loss_owners
#print axioms actual_at_most_two_loss_centres_original_pair_unique
#print axioms actual_at_most_two_loss_centres_opposite_injective
#print axioms actual_at_most_two_loss_centres_duplicate_debt_no_reuse
#print axioms actual_at_most_two_loss_centres_all_subfamilies_hall_iff_exterior
#print axioms actual_at_most_two_loss_centres_payment_iff_nonlocal

end OrderedEdgeColoring
end JSP000404Research
