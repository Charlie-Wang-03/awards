import JSP000404Research.PlanarDirectionBridge
import Mathlib.Algebra.Ring.Periodic

/-!
# Rotating projection curves of a forward angular lift

Projection onto the perpendicular of the rotating direction gives continuous antiperiodic
wire curves. Positive polar edge representations identify every intersection time exactly,
modulo the half-turn period.
-/

namespace JSP000404Research

noncomputable def projectionWireCurve (base lam : ℝ) (point : Plane) (time : ℝ) : ℝ :=
  point 0 * Real.sin (base + lam * time) - point 1 * Real.cos (base + lam * time)

theorem projectionWireCurve_continuous (base lam : ℝ) (point : Plane) :
    Continuous (projectionWireCurve base lam point) := by
  unfold projectionWireCurve
  fun_prop

theorem projectionWireCurve_antiperiodic (base lam period : ℝ) (point : Plane)
    (hscale : lam * period = Real.pi) :
    Function.Antiperiodic (projectionWireCurve base lam point) period := by
  intro time
  have hangle : base + lam * (time + period) = (base + lam * time) + Real.pi := by
    linarith [mul_add lam time period]
  simp only [projectionWireCurve, hangle, Real.sin_add_pi, Real.cos_add_pi]
  ring

namespace ForwardAngleLift

variable {V : Type*} [LinearOrder V] {p : V → Plane} {base : ℝ}
variable (F : ForwardAngleLift p base)

theorem projectionWireCurve_difference {i j : V} (hij : i < j) (lam time : ℝ) :
    projectionWireCurve base lam (p j) time - projectionWireCurve base lam (p i) time =
      F.rho i j * Real.sin (base + lam * time - F.theta i j) := by
  have hx := congrArg (fun q : Plane ↦ q 0) (F.repr hij)
  have hy := congrArg (fun q : Plane ↦ q 1) (F.repr hij)
  simp [rayDirection] at hx hy
  simp only [projectionWireCurve, Real.sin_sub]
  linear_combination Real.sin (base + lam * time) * hx - Real.cos (base + lam * time) * hy

theorem projectionWireCurve_at_event {i j : V} (hij : i < j) {lam : ℝ} (hlam : lam ≠ 0) :
    projectionWireCurve base lam (p i) ((F.theta i j - base) / lam) =
      projectionWireCurve base lam (p j) ((F.theta i j - base) / lam) := by
  have h := F.projectionWireCurve_difference hij lam ((F.theta i j - base) / lam)
  have hangle : base + lam * ((F.theta i j - base) / lam) - F.theta i j = 0 := by
    field_simp
    ring
  rw [hangle, Real.sin_zero, mul_zero] at h
  linarith

theorem projectionWireCurve_crossing {i j : V} (hij : i < j)
    {lam period : ℝ} (hlam : 0 < lam) (hscale : lam * period = Real.pi) (time : ℝ)
    (hcross : projectionWireCurve base lam (p i) time =
      projectionWireCurve base lam (p j) time) :
    ∃ k : ℤ, time = (F.theta i j - base) / lam + (k : ℝ) * period := by
  have hdifference := F.projectionWireCurve_difference hij lam time
  have hsin : Real.sin (base + lam * time - F.theta i j) = 0 := by
    rw [← hcross, sub_self] at hdifference
    exact (mul_eq_zero.mp hdifference.symm).resolve_left (ne_of_gt (F.rho_pos hij))
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin
  refine ⟨k, ?_⟩
  apply (mul_left_inj' (ne_of_gt hlam)).mp
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hlam)]
  calc
    time * lam = F.theta i j - base + (k : ℝ) * Real.pi := by linarith
    _ = F.theta i j - base + (k : ℝ) * period * lam := by rw [← hscale]; ring

#print axioms projectionWireCurve_at_event
#print axioms projectionWireCurve_crossing

end ForwardAngleLift
end JSP000404Research
