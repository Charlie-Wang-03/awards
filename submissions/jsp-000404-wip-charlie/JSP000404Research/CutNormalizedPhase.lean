import JSP000404Research.CutProjectiveBandPartition
import Mathlib.Tactic

/-!
# Canonical normalized coordinate versus a projective cut phase

For phase phi=t*c/pi, the cut-normalized coordinate of one ray is simply

  canonical - phi         above the cut,
  canonical + t - phi     below the cut.

These affine identities are the algebraic glue for returning a cut-wrap seam
to its canonical projective gap.
-/

namespace JSP000404Research

theorem cutNormalizedRayTheta_eq_normalized_sub_phase_of_ge
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t : ℝ)
    {c : ℝ} {i : V} (j : OtherVertex i)
    (hge : c ≤ rayThetaAt hp i j) :
    cutNormalizedRayTheta hp t c i j =
      normalizedRayTheta hp t i j -
        t * c / Real.pi := by
  rw [cutRayTheta_eq_sub_of_ge hp hge]
  unfold cutNormalizedRayTheta normalizedRayTheta
  ring

theorem cutNormalizedRayTheta_eq_normalized_add_period_sub_phase_of_lt
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t : ℝ)
    {c : ℝ} {i : V} (j : OtherVertex i)
    (hlt : rayThetaAt hp i j < c) :
    cutNormalizedRayTheta hp t c i j =
      normalizedRayTheta hp t i j + t -
        t * c / Real.pi := by
  rw [cutRayTheta_eq_add_pi_sub_of_lt hp hlt]
  unfold cutNormalizedRayTheta normalizedRayTheta
  field_simp [Real.pi_ne_zero]
  ring

#print axioms cutNormalizedRayTheta_eq_normalized_sub_phase_of_ge
#print axioms cutNormalizedRayTheta_eq_normalized_add_period_sub_phase_of_lt

end JSP000404Research
