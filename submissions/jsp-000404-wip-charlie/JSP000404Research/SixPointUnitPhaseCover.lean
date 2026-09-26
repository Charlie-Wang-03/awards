import JSP000404Research.SixPointCriticalPhaseCover
import JSP000404Research.SixPointUnitGapBudget
import Mathlib.Tactic

/-!
# Ten-slot phase-cover terminal for the six-point profile

The six-point top + five n-3 profile has at most ten unit quotient positions.
Every terminal critical transition gap has quotient one.

Therefore, once geometry assigns every irredundant critical obstruction to a
unit-gap slot (with nested fibres, or equivalently an injective slot map on the
irredundant cover), the phase-cover argument closes already for n>=5.

Indeed any lower-branch phase-circle cover needs at least 2n+2 intervals,
whereas only ten unit slots are available.
-/

namespace JSP000404Research

/-- Pure ten-slot obstruction. -/
theorem no_critical_phase_cover_of_at_most_ten_slots
    {I Slot : Type*}
    [DecidableEq I] [Fintype Slot]
    (alpha : Slot → ℝ)
    (s : I → ℝ)
    (slot : I → Slot)
    (S : Finset I)
    (n : ℕ) (delta : ℝ)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hslotCard : Fintype.card Slot ≤ 10)
    (hcoverLower :
      ∀ T : Finset I, T ⊆ S →
        PredicateCovers
          (InClosedInterval
            (fun k => criticalBadLeft
              (alpha (slot k)) (s k))
            (fun k => criticalBadRight
              (alpha (slot k)) delta))
          T →
        (n : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCovers
      (InClosedInterval
        (fun k => criticalBadLeft
          (alpha (slot k)) (s k))
        (fun k => criticalBadRight
          (alpha (slot k)) delta))
      S := by
  intro hcover
  let L : I → ℝ :=
    fun k => criticalBadLeft (alpha (slot k)) (s k)
  let R : I → ℝ :=
    fun k => criticalBadRight (alpha (slot k)) delta
  obtain ⟨T, hTS, hmin⟩ :=
    exists_irredundant_subcover
      (InClosedInterval L R) S hcover
  have hnested :
      ∀ {i j : I}, slot i = slot j →
        (L i ≤ L j ∧ R j ≤ R i) ∨
        (L j ≤ L i ∧ R i ≤ R j) := by
    intro i j hij
    exact critical_intervals_nested_of_same_alpha
      alpha s slot delta hij
  have hcardSlot :
      T.card ≤ Fintype.card Slot :=
    irredundant_card_le_slots_of_nested_fibres
      L R slot T hmin hnested
  have hcard10 : T.card ≤ 10 :=
    hcardSlot.trans hslotCard
  have hcoverReal :
      (n : ℝ) + delta ≤ (T.card : ℝ) * delta :=
    hcoverLower T hTS hmin.1
  have hneed :
      2 * n + 2 ≤ T.card :=
    phase_cover_count_lower
      (by omega) hdelta0 hdeltaHalf hcoverReal
  omega

/-- Equivalent variant when injectivity on an irredundant subcover is supplied
directly rather than through nested fibres. -/
theorem no_phase_cover_of_irredundant_slot_injection_ten
    {I Slot : Type*}
    [DecidableEq I] [Fintype Slot]
    (A : I → ℝ → Prop)
    (S : Finset I)
    (slot : I → Slot)
    (n : ℕ) (delta : ℝ)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hslotCard : Fintype.card Slot ≤ 10)
    (hinj :
      ∀ T : Finset I,
        T ⊆ S →
        IrredundantCover A T →
        ∀ {i j}, i ∈ T → j ∈ T →
          slot i = slot j → i = j)
    (hcoverLower :
      ∀ T : Finset I, T ⊆ S →
        PredicateCovers A T →
        (n : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCovers A S := by
  intro hcover
  obtain ⟨T, hTS, hmin⟩ :=
    exists_irredundant_subcover A S hcover
  let f : {i : I // i ∈ T} → Slot :=
    fun i => slot i.1
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact hinj T hTS hmin i.2 j.2 hij
  have hcard :
      T.card ≤ Fintype.card Slot := by
    have h :=
      Fintype.card_le_of_injective f hf
    simpa [f] using h
  have hten : T.card ≤ 10 :=
    hcard.trans hslotCard
  have hcoverReal :=
    hcoverLower T hTS hmin.1
  have hneed :=
    phase_cover_count_lower
      (by omega : 1 ≤ n)
      hdelta0 hdeltaHalf hcoverReal
  omega

#print axioms no_critical_phase_cover_of_at_most_ten_slots
#print axioms no_phase_cover_of_irredundant_slot_injection_ten

end JSP000404Research
