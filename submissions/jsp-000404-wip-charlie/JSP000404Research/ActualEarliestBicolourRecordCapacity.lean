import JSP000404Research.ActualEarliestActiveRectangleNecessary
import Mathlib.Tactic

/-!
# Only genuinely bichromatic-owner original records can pay local eighth debt

No original earliest-prior source collision record is automatically a
true exterior Boolean hole.  This file constructs a STRICTLY FILTERED
source-native candidate set: only those original records with distinct
projected-loss owners which are BOTH active at BOTH original collision
colours.  Every genuine locally payable hole is in its opposite image.

This provides a quantitative ceiling on all locally available original
eighth-lane credit.  It does NOT create those holes, and does NOT assume
an injection from record sources into nonlocal payment credits.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Original eighth-debt records possessing a genuinely shared two-colour
rectangle of two *original* projected-loss centres.  This is a
potentially strict subset of the original earliest-prior record set. -/
noncomputable def actualEarliestBicolourRecordCandidates
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    Finset (Fin n × Fin n × (Fin n → Bool)) :=
  (actualEarliestLossCollisionRecords C exponent choice).filter
    (fun a => ∃ v u : V,
      v ≠ u ∧
      v ∈ projectedLossVertices C exponent ∧
      u ∈ projectedLossVertices C exponent ∧
      a.1 ∈ retainedActive C v ∧
      a.2.1 ∈ retainedActive C v ∧
      a.1 ∈ retainedActive C u ∧
      a.2.1 ∈ retainedActive C u)

/-- Every actually eligible exterior true-hole credit of the ORIGINAL
earliest-prior eighth class is the diagonal image of a record with TWO
ACTUAL distinct owners sharing BOTH distinct collision colours. -/
theorem actual_earliest_eligible_local_holes_subset_bicolour_record_image
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v) :
    actualLossEarliestEligibleLocalHoles C exponent choice ⊆
      (actualEarliestBicolourRecordCandidates C exponent choice).image
        (fun a : Fin n × Fin n × (Fin n → Bool) =>
          flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1) := by
  classical
  intro q hq
  have hpair : q ∈
      actualLossEarliestOppositeCandidateWords C exponent choice ∩
        lossLedgerOutsideTranslatedTrueHoles C exponent choice := hq
  obtain ⟨himage, hhole⟩ := Finset.mem_inter.mp hpair
  change q ∈
    (actualEarliestLossCollisionRecords C exponent choice).image
      (fun a : Fin n × Fin n × (Fin n → Bool) =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1) at himage
  obtain ⟨a, ha, hqa⟩ := Finset.mem_image.mp himage
  have hqRecord :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 ∈
        lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
    rw [hqa]
    exact hhole
  obtain ⟨v,u,hne,hv,hu,hvc,hvd,huc,hud,_,_⟩ :=
    actual_earliest_exterior_record_has_two_biactive_owners
      C exponent choice hchoice a ha hqRecord
  apply Finset.mem_image.mpr
  refine ⟨a, ?_, hqa⟩
  exact Finset.mem_filter.mpr
    ⟨ha, ⟨v,u,hne,hv,hu,hvc,hvd,huc,hud⟩⟩

/-- Source-native counting ceiling: no TRUE local eighth-lane credit
can exceed the number of original records passing the simultaneous
two-owner/two-colour gate.  This count does NOT assume candidate
nonreuse or treat a covered diagonal as a true hole. -/
theorem actual_earliest_eligible_local_holes_card_le_bicolour_records
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v) :
    (actualLossEarliestEligibleLocalHoles C exponent choice).card ≤
      (actualEarliestBicolourRecordCandidates C exponent choice).card := by
  classical
  calc
    (actualLossEarliestEligibleLocalHoles C exponent choice).card ≤
        ((actualEarliestBicolourRecordCandidates C exponent choice).image
          (fun a : Fin n × Fin n × (Fin n → Bool) =>
            flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)).card :=
      Finset.card_le_card
        (actual_earliest_eligible_local_holes_subset_bicolour_record_image
          C exponent choice hchoice)
    _ ≤ (actualEarliestBicolourRecordCandidates C exponent choice).card :=
      Finset.card_image_le

#print axioms actual_earliest_eligible_local_holes_subset_bicolour_record_image
#print axioms actual_earliest_eligible_local_holes_card_le_bicolour_records

end OrderedEdgeColoring
end JSP000404Research
