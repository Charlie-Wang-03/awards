import JSP000404Research.CyclicCriticalUnitPhase
import JSP000404Research.CutMergedOneExceptionTerminal
import Mathlib.Tactic

/-!
# Convert normalized cyclic phases into actual projective cuts

The phase-counting backend works in normalized coordinates x in [0,t).
The cut projective-band construction is parameterized by a physical cut
c in [0,pi), queried through the phase t*c/pi.

For t>0 the conversion is exact:

  c = pi*x/t.

This file packages that algebra and feeds the eleven-phase six-point terminal
directly into an actual projective cut.
-/

namespace JSP000404Research

def projectiveCutOfPhase (t x : ℝ) : ℝ :=
  Real.pi * x / t

theorem projectiveCutOfPhase_nonneg
    {t x : ℝ}
    (ht : 0 < t)
    (hx0 : 0 ≤ x) :
    0 ≤ projectiveCutOfPhase t x := by
  unfold projectiveCutOfPhase
  positivity

theorem projectiveCutOfPhase_lt_pi
    {t x : ℝ}
    (ht : 0 < t)
    (hxt : x < t) :
    projectiveCutOfPhase t x < Real.pi := by
  unfold projectiveCutOfPhase
  rw [div_lt_iff₀ ht]
  nlinarith [Real.pi_pos]

theorem phase_projectiveCutOfPhase
    {t x : ℝ}
    (ht : 0 < t) :
    t * projectiveCutOfPhase t x / Real.pi = x := by
  unfold projectiveCutOfPhase
  field_simp [ne_of_gt ht, Real.pi_ne_zero]
  ring

/-- For the six-point terminal with n>=5, one of the canonical eleven
sample phases yields an actual cut which is uncovered by every global cyclic
q=1 critical slot. -/
theorem exists_critical_uncovered_eleven_cut
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = n - 3) :
    ∃ r : Fin 11,
      let c := projectiveCutOfPhase t (elevenPhase t r)
      0 ≤ c ∧
      c < Real.pi ∧
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u (t * c / Real.pi) := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  obtain ⟨r, hr⟩ :=
    exists_uncovered_elevenPhase_of_six_point_terminal
      C hn4 hn5 hdelta0 hdeltaHalf ht
      hcard top hTop hMin
  refine ⟨r, ?_, ?_, ?_⟩
  · exact projectiveCutOfPhase_nonneg
      htpos (elevenPhase_nonneg htpos.le r)
  · exact projectiveCutOfPhase_lt_pi
      htpos (elevenPhase_lt_t htpos r)
  · intro u hbad
    apply hr u
    simpa [phase_projectiveCutOfPhase htpos] using hbad

#print axioms phase_projectiveCutOfPhase
#print axioms exists_critical_uncovered_eleven_cut

end JSP000404Research
