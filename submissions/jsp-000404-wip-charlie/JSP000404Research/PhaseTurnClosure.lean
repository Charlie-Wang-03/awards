import JSP000404Research.HullTurnBudget
import JSP000404Research.PhaseObstruction
import Mathlib.Tactic

/-!
# Final arithmetic shell for the lower-branch phase argument

This module composes the two already-closed reductions:

* normalized convex-hull turn slots give at most 2n obstruction components;
* at most 2n intervals of length delta cannot cover the phase circle of
  circumference n+delta when 0 <= delta < 1/2.

Consequently the remaining geometry may be packaged in exactly three facts:

1. nonnegative normalized hull turns sum to 2(n+delta);
2. the number of obstruction slots assigned to each hull turn is at most its
   natural floor;
3. if every phase is bad, those obstruction slots yield a delta-cover of the
   full phase circle.

No additional arithmetic is required after those facts are supplied.
-/

namespace JSP000404Research

open scoped BigOperators

theorem exists_good_phase_of_turn_slot_cover
    {Phase I : Type*} [Nonempty Phase] [Fintype I]
    (Bad : Phase → Prop)
    (turn : I → ℝ) (slots : I → ℕ)
    (n : ℕ) (delta : ℝ)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hturn0 : ∀ i, 0 ≤ turn i)
    (hturnsum : (∑ i, turn i) = 2 * ((n : ℝ) + delta))
    (hslots : ∀ i, slots i ≤ Nat.floor (turn i))
    (hallbad_cover :
      (∀ phase, Bad phase) →
        (n : ℝ) + delta ≤
          ((∑ i, slots i : ℕ) : ℝ) * delta) :
    ∃ phase, ¬ Bad phase := by
  have hcount :
      (∑ i, slots i) ≤ 2 * n :=
    obstruction_count_le_of_turn_slots
      turn slots n delta hturn0 hturnsum hdelta hslots
  exact exists_good_phase_of_bad_cover_count
    Bad hn hdelta0 hdelta hcount hallbad_cover

/-- Contradiction form useful when the geometric phase argument is naturally
written under an all-bad assumption. -/
theorem not_all_bad_of_turn_slot_cover
    {Phase I : Type*} [Nonempty Phase] [Fintype I]
    (Bad : Phase → Prop)
    (turn : I → ℝ) (slots : I → ℕ)
    (n : ℕ) (delta : ℝ)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hturn0 : ∀ i, 0 ≤ turn i)
    (hturnsum : (∑ i, turn i) = 2 * ((n : ℝ) + delta))
    (hslots : ∀ i, slots i ≤ Nat.floor (turn i))
    (hallbad_cover :
      (∀ phase, Bad phase) →
        (n : ℝ) + delta ≤
          ((∑ i, slots i : ℕ) : ℝ) * delta) :
    ¬ ∀ phase, Bad phase := by
  intro hall
  obtain ⟨phase, hgood⟩ :=
    exists_good_phase_of_turn_slot_cover
      Bad turn slots n delta hn hdelta0 hdelta
      hturn0 hturnsum hslots hallbad_cover
  exact hgood (hall phase)

#print axioms exists_good_phase_of_turn_slot_cover
#print axioms not_all_bad_of_turn_slot_cover

end JSP000404Research
