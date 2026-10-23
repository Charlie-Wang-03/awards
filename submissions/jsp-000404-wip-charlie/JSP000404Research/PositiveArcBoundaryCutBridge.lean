import JSP000404Research.PositiveToCriticalPhaseBridge
import JSP000404Research.UncoveredBoundaryColoring
import Mathlib.Tactic

/-! A TRUE full-positive-arc-safe physical phase provides a coherent
boundary two-colouring at every corresponding geometric cut. This uses the
actual cut partition and its canonical critical gap witnesses. The remaining
global Boolean-hole/surplus payment is independent and not asserted here. -/
namespace JSP000404Research

theorem positive_deltaArc_safe_implies_boundary_cut_separation
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta c x : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (hphase : t * c / Real.pi = x)
    (hsafe : ∀ v : GlobalPositiveGapSlot C t,
      ¬ CyclicDeltaArcAtAnyBase t delta
        (globalPositiveGapStart C t v) x) :
    let htop : t < (n + 1 : ℕ) := by rw [ht]; push_cast; linarith
    let P := cutProjectiveBandPartition hp hcap htpos hlam hc0 hcpi n htop
    let wrapBit := cutBoundaryWrapBit (delta := delta) hp n htpos htop hc0 hcpi
    ∀ {u v : V}, u < v →
      ((P.edgeColor u v).val = 0 ∨ (P.edgeColor u v).val = n) →
      wrapBit u ≠ wrapBit v := by
  have huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt C t delta u
          (t * c / Real.pi) := by
    intro u hbad
    have hcrit :=
      full_positive_deltaArc_safe_implies_critical_unit_safe
        C t delta x hsafe u
    apply hcrit
    simpa only [hphase] using hbad
  exact cutBoundaryWrapBit_separates
    hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
    hc0 hcpi huncovered

#print axioms positive_deltaArc_safe_implies_boundary_cut_separation

end JSP000404Research
