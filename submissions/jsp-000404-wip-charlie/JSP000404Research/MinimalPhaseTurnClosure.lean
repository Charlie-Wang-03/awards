import JSP000404Research.MinimalPhaseCover
import JSP000404Research.GlobalTurnSlots
import Mathlib.Tactic

/-!
# Minimal-cover + global-turn closure

This is the final combinatorial shell of the current lower-branch phase route.

Suppose a finite family of closed bad-phase intervals covers the whole phase
circle.  Extract an inclusion-irredundant subcover T.

Assume every obstruction has been assigned to a finite global turn-slot type,
and any two intervals assigned to the same slot are nested.  MinimalPhaseCover
then makes the slot map injective on T, hence

  |T| <= number of turn slots.

If the slot count is bounded by the normalized total hull turning path,

  card Slot <= 2(n+delta),

then integer rounding in the lower branch gives card Slot <= 2n.

But a delta-cover of a phase circle of circumference n+delta needs at least
2n+2 intervals.  Contradiction.

Thus after this file, the only genuinely geometric tasks are:

1. construct the finite turn-slot assignment for critical obstructions;
2. prove same-slot bad intervals are nested;
3. supply the standard interval-length cover lower bound.
-/

namespace JSP000404Research

/-- A phase cover by nested-fibre obstructions is impossible once its slot
type fits into the global lower-branch turn budget. -/
theorem no_phase_cover_of_nested_global_turn_slots
    {I Slot : Type*}
    [DecidableEq I] [Fintype Slot]
    (L R : I → ℝ)
    (slot : I → Slot)
    (S : Finset I)
    (n : ℕ) (delta : ℝ)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hslotBudget :
      (Fintype.card Slot : ℝ) ≤
        2 * ((n : ℝ) + delta))
    (hnested :
      ∀ {i j : I}, slot i = slot j →
        (L i ≤ L j ∧ R j ≤ R i) ∨
        (L j ≤ L i ∧ R i ≤ R j))
    (hcoverLower :
      ∀ T : Finset I, T ⊆ S →
        PredicateCovers (InClosedInterval L R) T →
        (n : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCovers (InClosedInterval L R) S := by
  intro hcover
  obtain ⟨T, hTS, hmin⟩ :=
    exists_irredundant_subcover
      (InClosedInterval L R) S hcover
  have hcardSlot :
      T.card ≤ Fintype.card Slot :=
    irredundant_card_le_slots_of_nested_fibres
      L R slot T hmin hnested
  have hslotNat :
      Fintype.card Slot ≤ 2 * n :=
    hull_count_upper hdeltaHalf hslotBudget
  have hcardUpper :
      T.card ≤ 2 * n :=
    hcardSlot.trans hslotNat
  have hcoverReal :
      (n : ℝ) + delta ≤ (T.card : ℝ) * delta :=
    hcoverLower T hTS hmin.1
  have hcardLower :
      2 * n + 2 ≤ T.card :=
    phase_cover_count_lower
      hn hdelta0 hdeltaHalf hcoverReal
  omega

/-- Equivalent existence form when badness is exactly membership in one of the
critical intervals from S. -/
theorem exists_phase_outside_all_obstructions
    {I Slot : Type*}
    [DecidableEq I] [Fintype Slot]
    (L R : I → ℝ)
    (slot : I → Slot)
    (S : Finset I)
    (n : ℕ) (delta : ℝ)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hslotBudget :
      (Fintype.card Slot : ℝ) ≤
        2 * ((n : ℝ) + delta))
    (hnested :
      ∀ {i j : I}, slot i = slot j →
        (L i ≤ L j ∧ R j ≤ R i) ∨
        (L j ≤ L i ∧ R i ≤ R j))
    (hcoverLower :
      ∀ T : Finset I, T ⊆ S →
        PredicateCovers (InClosedInterval L R) T →
        (n : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ∃ x : ℝ, ∀ i, i ∈ S →
      ¬ InClosedInterval L R i x := by
  by_contra hnone
  push_neg at hnone
  have hcover : PredicateCovers (InClosedInterval L R) S := by
    intro x
    obtain ⟨i, hiS, hi⟩ := hnone x
    exact ⟨i, hiS, hi⟩
  exact no_phase_cover_of_nested_global_turn_slots
    L R slot S n delta
    hn hdelta0 hdeltaHalf
    hslotBudget hnested hcoverLower hcover

#print axioms no_phase_cover_of_nested_global_turn_slots
#print axioms exists_phase_outside_all_obstructions

end JSP000404Research
