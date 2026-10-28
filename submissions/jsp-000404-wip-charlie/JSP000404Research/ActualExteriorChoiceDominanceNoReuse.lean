import JSP000404Research.ActualExteriorChoiceColourFibrePacking
import JSP000404Research.ActualEighthNoBicolourHallHardStop
import Mathlib.Tactic

/-!
# Original eighth-debt exact local payment under a dominant chosen colour

At most ONE bichromatic original projected-loss centre may choose
a colour other than c0. This permits arbitrarily many bichromatic
loss centres sharing c0, so it is distinct from the old <=3 total
bichromatic-centre bound.

Every true exterior opposite candidate then has at most ONE genuine
earliest-prior collision record. Consequently every original record
whose opposite word is genuinely exterior is ALREADY uniquely and
legally payable locally; source selection/duplicate loss is unnecessary
for that entire real-payable subfamily.

This is a necessary/conditional genuine local nonreuse certificate.
It does NOT prove the remaining seven-source/nonlocal credit budget.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Dominance of one genuine chosen loss colour forbids repeated
ORIGINAL earliest-prior records at the same TRUE exterior hole,
regardless of the total number of bichromatic loss centres. -/
theorem actual_eighth_true_exterior_no_reuse_of_one_off_dominant_choice
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (c0 : Fin n)
    (hsmall :
      ((projectedLossVertices C exponent).filter (fun v =>
        (∃ c d : Fin n, c ≠ d ∧
          c ∈ retainedActive C v ∧
          d ∈ retainedActive C v) ∧ choice v ≠ c0)).card ≤ 1)
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
  classical
  let q := flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  let F := actualLossOppositeCandidateFibre C exponent choice q
  have haF : a ∈ F :=
    Finset.mem_filter.mpr ⟨ha, rfl⟩
  have hbF : b ∈ F :=
    Finset.mem_filter.mpr ⟨hb, hopposite.symm⟩
  have hle : F.card ≤ 1 := by
    exact (actual_true_exterior_fibre_le_bichromatic_away_from_one_chosen_colour
      C exponent choice hchoice q hq c0).trans hsmall
  by_contra hab
  have htwo : ({a, b} : Finset (Fin n × Fin n × (Fin n → Bool))).card = 2 := by
    simp [hab]
  have hsub : ({a, b} : Finset (Fin n × Fin n × (Fin n → Bool))) ⊆ F := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact haF
    · exact hbF
  have hmin := Finset.card_le_card hsub
  omega

/-- Under one dominant chosen colour, the ORIGINAL opposite map
is literally injective on ALL genuine locally-payable eighth source
records, not only on a selected one-per-hole section. -/
theorem actual_eighth_all_payable_records_injOn_of_one_off_dominant_choice
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (c0 : Fin n)
    (hsmall :
      ((projectedLossVertices C exponent).filter (fun v =>
        (∃ c d : Fin n, c ≠ d ∧
          c ∈ retainedActive C v ∧
          d ∈ retainedActive C v) ∧ choice v ≠ c0)).card ≤ 1) :
    Set.InjOn
      (fun a : Fin n × Fin n × (Fin n → Bool) =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)
      (actualEighthLocallyPayableRecords C exponent choice : Set _) := by
  classical
  intro a ha b hb heq
  change a ∈ actualEighthLocallyPayableRecords C exponent choice at ha
  change b ∈ actualEighthLocallyPayableRecords C exponent choice at hb
  obtain ⟨haRecord, hq⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbRecord, _⟩ := Finset.mem_filter.mp hb
  exact actual_eighth_true_exterior_no_reuse_of_one_off_dominant_choice
    C exponent choice hchoice c0 hsmall a b haRecord hbRecord heq hq

/-- Exact genuine original-source payment capacity under dominant
choice: EVERY locally payable original eighth collision source can
receive its distinct real outside-translated true-hole target. -/
theorem actual_eighth_all_payable_card_eq_true_holes_of_one_off_dominant_choice
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    (c0 : Fin n)
    (hsmall :
      ((projectedLossVertices C exponent).filter (fun v =>
        (∃ c d : Fin n, c ≠ d ∧
          c ∈ retainedActive C v ∧
          d ∈ retainedActive C v) ∧ choice v ≠ c0)).card ≤ 1) :
    (actualEighthLocallyPayableRecords C exponent choice).card =
      (actualLossEarliestEligibleLocalHoles C exponent choice).card := by
  classical
  let f : (Fin n × Fin n × (Fin n → Bool)) → (Fin n → Bool) :=
    fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  have hinj : Set.InjOn f
      (actualEighthLocallyPayableRecords C exponent choice : Set _) :=
    actual_eighth_all_payable_records_injOn_of_one_off_dominant_choice
      C exponent choice hchoice c0 hsmall
  calc
    (actualEighthLocallyPayableRecords C exponent choice).card =
        ((actualEighthLocallyPayableRecords C exponent choice).image f).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = (actualLossEarliestEligibleLocalHoles C exponent choice).card := by
      rw [actual_eighth_payable_records_image_eq_true_local_holes]

#print axioms actual_eighth_true_exterior_no_reuse_of_one_off_dominant_choice
#print axioms actual_eighth_all_payable_records_injOn_of_one_off_dominant_choice
#print axioms actual_eighth_all_payable_card_eq_true_holes_of_one_off_dominant_choice

end OrderedEdgeColoring
end JSP000404Research
