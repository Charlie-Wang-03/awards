import JSP000404Research.PositiveGapThirteenSlotPhase
import Mathlib.Tactic

/-! Full periodic delta-arc escape for original positive quotient-gap slots.
Unlike prior certificates this avoids the entire width-delta arc, not only
the narrower physical bad subinterval. Global resource payment stays open. -/

namespace JSP000404Research

theorem positive_gap_exists_full_deltaArc_free_sample
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ} (M : ℕ)
    (ht : 0 < t) (hdelta0 : 0 ≤ delta)
    (hM : 2 ≤ M) (hsep : delta < t / (M : ℝ))
    (hcard : Fintype.card (GlobalPositiveGapSlot C t) < M) :
    ∃ r : Fin M, ∀ u : GlobalPositiveGapSlot C t,
      ¬ CyclicDeltaArcAtAnyBase t delta
        (globalPositiveGapStart C t u) (cyclicSamplePhase t M r) := by
  classical
  by_contra hnone
  push_neg at hnone
  let slot : Fin M → GlobalPositiveGapSlot C t :=
    fun r => Classical.choose (hnone r)
  have hbad : ∀ r : Fin M,
      CyclicDeltaArcAtAnyBase t delta
        (globalPositiveGapStart C t (slot r))
        (cyclicSamplePhase t M r) := by
    intro r
    exact Classical.choose_spec (hnone r)
  have hinj : Function.Injective slot := by
    intro r s hrs
    have hrArc := hbad r
    have hsArc : CyclicDeltaArcAtAnyBase t delta
        (globalPositiveGapStart C t (slot r))
        (cyclicSamplePhase t M s) := by
      simpa only [hrs] using hbad s
    exact cyclicSamplePhase_injective_on_same_anyBaseArc
      ht hM hdelta0 hsep hrArc hsArc
  have hcount : M ≤ Fintype.card (GlobalPositiveGapSlot C t) := by
    simpa using (Fintype.card_le_of_injective slot hinj)
  omega

#print axioms positive_gap_exists_full_deltaArc_free_sample

end JSP000404Research
