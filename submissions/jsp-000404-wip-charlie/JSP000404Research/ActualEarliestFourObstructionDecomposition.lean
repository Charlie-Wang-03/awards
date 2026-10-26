import JSP000404Research.ActualEarliestOriginalNonlocalEligibility
import Mathlib.Tactic

/-!
# Full original eighth-source NONLOCAL obstruction: a four-way IFF

For every REAL earliest-prior source collision, the opposite word is
an INELIGIBLE original exterior-hole candidate exactly when at least
one of FOUR explicit obstructions occurs:

1. missing cross-active colour at the first genuine owner;
2. missing cross-active colour at the second genuine owner;
3. coverage by a THIRD original retained completion cube;
4. capture by any actual translated-loss slice.

This follows from the previously certified exact true-hole eligibility
IFF.  It is not a global eight-class allocation theorem, and it
introduces no synthetic holes or assumptions of nonreuse.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Four EXHAUSTIVE and NECESSARY/SUFFICIENT concrete reasons why an
original eighth-debt opposite candidate contributes to O \\ H instead
of being a genuine outside-translated true hole. -/
theorem actual_earliest_record_nonlocal_defect_iff_four_obstructions
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (a : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice)
    (v u : V)
    (hv : v ∈ lossCoordinateSlice C exponent choice a.1)
    (hu : u ∈ lossCoordinateSlice C exponent choice a.2.1)
    (hw : a.2.2 ∈ translatedCompletionWords C v a.1)
    (hz : a.2.2 ∈ translatedCompletionWords C u a.2.1) :
    let q := flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
    q ∈ (actualLossEarliestOppositeCandidateWords C exponent choice \
      lossLedgerOutsideTranslatedTrueHoles C exponent choice) ↔
      a.2.1 ∉ retainedActive C v ∨
      a.1 ∉ retainedActive C u ∨
      (∃ z : V, z ≠ v ∧ z ≠ u ∧
        q ∈ retainedCompletionWords C z) ∨
      q ∈ translatedLossAllCoordinateWords C exponent choice := by
  classical
  dsimp only
  let q := flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  change q ∈ (actualLossEarliestOppositeCandidateWords C exponent choice \
    lossLedgerOutsideTranslatedTrueHoles C exponent choice) ↔
      a.2.1 ∉ retainedActive C v ∨
      a.1 ∉ retainedActive C u ∨
      (∃ z : V, z ≠ v ∧ z ≠ u ∧
        q ∈ retainedCompletionWords C z) ∨
      q ∈ translatedLossAllCoordinateWords C exponent choice
  have hcandidate :
      q ∈ actualLossEarliestOppositeCandidateWords C exponent choice :=
    Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have heligible :
      q ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice ↔
        a.2.1 ∈ retainedActive C v ∧
        a.1 ∈ retainedActive C u ∧
        (∀ z : V, z ≠ v → z ≠ u →
          q ∉ retainedCompletionWords C z) ∧
        q ∉ translatedLossAllCoordinateWords C exponent choice :=
    actual_earliest_record_exterior_iff_full_owner_eligibility
      C exponent choice a ha v u hv hu hw hz
  have hdemorgan :
      ¬ (a.2.1 ∈ retainedActive C v ∧
        a.1 ∈ retainedActive C u ∧
        (∀ z : V, z ≠ v → z ≠ u →
          q ∉ retainedCompletionWords C z) ∧
        q ∉ translatedLossAllCoordinateWords C exponent choice) ↔
      a.2.1 ∉ retainedActive C v ∨
      a.1 ∉ retainedActive C u ∨
      (∃ z : V, z ≠ v ∧ z ≠ u ∧
        q ∈ retainedCompletionWords C z) ∨
      q ∈ translatedLossAllCoordinateWords C exponent choice := by
    push_neg
    tauto
  calc
    q ∈ (actualLossEarliestOppositeCandidateWords C exponent choice \
      lossLedgerOutsideTranslatedTrueHoles C exponent choice) ↔
        ¬ q ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
          simp only [Finset.mem_sdiff, hcandidate, true_and]
    _ ↔ ¬ (a.2.1 ∈ retainedActive C v ∧
      a.1 ∈ retainedActive C u ∧
      (∀ z : V, z ≠ v → z ≠ u →
        q ∉ retainedCompletionWords C z) ∧
      q ∉ translatedLossAllCoordinateWords C exponent choice) :=
        not_congr heligible
    _ ↔ _ := hdemorgan

#print axioms actual_earliest_record_nonlocal_defect_iff_four_obstructions

end OrderedEdgeColoring
end JSP000404Research
