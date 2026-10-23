import JSP000404Research.SixPointFullDeltaArcDichotomy
import JSP000404Research.CyclicCriticalUnitPhase
import Mathlib.Tactic

/-! Exact embedding of all quotient-one critical slots into positive-gap
slots, preserving their original canonical start. A full delta-arc-safe
phase therefore avoids every critical unit-gap bad phase at the same x.
No Boolean-hole/dyadic global payment is asserted. -/
namespace JSP000404Research

noncomputable def unitGapAsPositiveGap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ) (u : GlobalUnitGapSlot C t) :
    GlobalPositiveGapSlot C t :=
  ⟨u.1, ⟨u.2.1, by
    change centreQuotient (C u.1) t u.2.1 ≠ 0
    rw [u.2.2]
    decide⟩⟩

theorem unitGapAsPositiveGap_start
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ) (u : GlobalUnitGapSlot C t) :
    globalPositiveGapStart C t (unitGapAsPositiveGap C t u) =
      globalUnitGapStart C t u := by
  unfold globalPositiveGapStart centrePositiveGapStart
    globalUnitGapStart centreUnitGapStart
    unitGapAsPositiveGap normalizedRayTheta
  ring

theorem full_positive_deltaArc_safe_implies_critical_unit_safe
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t delta x : ℝ)
    (hsafe : ∀ v : GlobalPositiveGapSlot C t,
      ¬ CyclicDeltaArcAtAnyBase t delta
        (globalPositiveGapStart C t v) x) :
    ∀ u : GlobalUnitGapSlot C t,
      ¬ GlobalCyclicCriticalUnitBadAt C t delta u x := by
  intro u hbad
  have hArc : CyclicDeltaArcAtAnyBase t delta
      (globalUnitGapStart C t u) x := by
    simpa only [CyclicDeltaArcAtAnyBase, CyclicDeltaArcAt] using
      (cyclicCriticalUnitBadAt_implies_deltaArc C hbad)
  apply hsafe (unitGapAsPositiveGap C t u)
  rwa [unitGapAsPositiveGap_start]

#print axioms unitGapAsPositiveGap_start
#print axioms full_positive_deltaArc_safe_implies_critical_unit_safe

end JSP000404Research
