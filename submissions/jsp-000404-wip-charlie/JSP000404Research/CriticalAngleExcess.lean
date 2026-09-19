import JSP000404Research.CriticalBadMass
import Mathlib.Tactic

/-!
# Critical bad width as large-angle excess

Let

  t = n + delta,
  pi = t * lam,

and let a critical transition have normalized projective width s.  The
corresponding large geometric angle is

  A = pi - s * lam.

Its bad-phase width is

  1 + delta - s.

Multiplying by lam gives the exact identity

  lam * (1 + delta - s)
    = A - (n - 1) * lam.

Thus the phase-cover problem can be phrased as a total excess-angle problem:
the sum of the amounts by which critical large angles exceed the baseline
`(n-1)*lam` must be strictly below pi.
-/

namespace JSP000404Research

/-- Exact algebraic conversion between critical bad width and excess above the
lower large-angle threshold. -/
theorem critical_bad_width_mul_eq_angle_excess
    {n : ℕ} {delta lam s angle : ℝ}
    (hpi : Real.pi = ((n : ℝ) + delta) * lam)
    (hangle : angle = Real.pi - s * lam) :
    lam * criticalBadWidth delta s =
      angle - ((n : ℝ) - 1) * lam := by
  rw [hangle, hpi]
  unfold criticalBadWidth
  ring

/-- Criticality bounds turn the angle excess into a nonnegative quantity no
larger than `delta*lam`. -/
theorem critical_angle_excess_bounds
    {n : ℕ} {delta lam s angle : ℝ}
    (hlam0 : 0 ≤ lam)
    (hs1 : 1 ≤ s)
    (hsTop : s ≤ 1 + delta)
    (hpi : Real.pi = ((n : ℝ) + delta) * lam)
    (hangle : angle = Real.pi - s * lam) :
    0 ≤ angle - ((n : ℝ) - 1) * lam ∧
      angle - ((n : ℝ) - 1) * lam ≤ delta * lam := by
  have hid :=
    critical_bad_width_mul_eq_angle_excess
      (n := n) (delta := delta) (lam := lam)
      (s := s) (angle := angle) hpi hangle
  rw [← hid]
  constructor
  · apply mul_nonneg hlam0
    unfold criticalBadWidth
    linarith
  · have hw :
        criticalBadWidth delta s ≤ delta := by
      unfold criticalBadWidth
      linarith
    exact mul_le_mul_of_nonneg_left hw hlam0

/-- If the normalized total bad mass is below the Sendov phase circumference,
then the corresponding physical total angle excess is below pi. -/
theorem physical_excess_lt_pi_of_bad_mass_lt_phase
    {C : Type*} [Fintype C]
    (bad : C → ℝ)
    {t lam : ℝ}
    (hlam : 0 < lam)
    (hpi : Real.pi = t * lam)
    (hbad : (∑ c, bad c) < t) :
    (∑ c, lam * bad c) < Real.pi := by
  rw [hpi]
  rw [← Finset.mul_sum]
  exact mul_lt_mul_of_pos_left hbad hlam

#print axioms critical_bad_width_mul_eq_angle_excess
#print axioms critical_angle_excess_bounds
#print axioms physical_excess_lt_pi_of_bad_mass_lt_phase

end JSP000404Research
