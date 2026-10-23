import JSP000404Research.PositiveGapFullDeltaArcEscape
import Mathlib.Tactic

/-! Original six-centre no-compensation geometric dichotomy, strengthened to
a phase outside every *full* positive-quotient delta arc at 13*delta<n.
This is not a global Boolean-hole payment certificate. -/
namespace JSP000404Research

theorem six_point_hard_top_two_support_two_or_full_deltaArc_escape
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hthreshold : 13 * delta < (n : ℝ))
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3)
    (hNoTop :
      SixPointNoCompensatedTopDeletion
        C (by rw [hcard]; omega) top t n) :
    (∃ a b : V,
      a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
      a ∉ topDeletionGainMinima C
        (by rw [hcard]; omega) top t ∧
      b ∉ topDeletionGainMinima C
        (by rw [hcard]; omega) top t ∧
      positiveSupport (centreQuotient (C a) t) = 2 ∧
      positiveSupport (centreQuotient (C b) t) = 2) ∨
    (∃ x : ℝ, 0 ≤ x ∧ x < t ∧
      ∀ u : GlobalPositiveGapSlot C t,
        ¬ CyclicDeltaArcAtAnyBase t delta
          (globalPositiveGapStart C t u) x) := by
  classical
  rcases six_point_hard_top_thirteen_slots_or_two_support_two
    hp hcap C hcard hn5 hdelta0 hdeltaHalf ht hlam
    top hTop hMin hNoTop with h13 | htwo
  · right
    have htpos : 0 < t :=
      sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
    have hsep : delta < t / 14 := by
      rw [ht]
      linarith
    obtain ⟨r, hr⟩ :=
      positive_gap_exists_full_deltaArc_free_sample C 14
        htpos hdelta0 (by omega : 2 ≤ 14) hsep (by omega)
    exact ⟨cyclicSamplePhase t 14 r,
      cyclicSamplePhase_nonneg htpos.le (by omega : 1 ≤ 14) r,
      cyclicSamplePhase_lt_t htpos (by omega : 1 ≤ 14) r, hr⟩
  · exact Or.inl htwo

#print axioms six_point_hard_top_two_support_two_or_full_deltaArc_escape

end JSP000404Research
