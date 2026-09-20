import JSP000404Research.FiniteProjectiveRays
import Mathlib.Tactic

/-!
# Exact angles between signed projective rays

For projective parameters theta and phi with |theta-phi| <= pi:

* equal signs give the ordinary angle |theta-phi|;
* opposite signs give the supplementary angle pi-|theta-phi|.

Consequently, under a cap angle <= pi-lambda, two opposite-signed rays whose
parameters satisfy theta <= phi must be separated by at least lambda.

This is the geometric mechanism behind "sign changes only on positive Sendov
quotient gaps".
-/

namespace JSP000404Research

open Real

theorem angle_signedRayDirection_eq_of_sign_eq
    {sigma tau : Bool} {theta phi : ℝ}
    (hsign : sigma = tau)
    (hdiff : |theta - phi| ≤ Real.pi) :
    InnerProductGeometry.angle
        (signedRayDirection sigma theta)
        (signedRayDirection tau phi) =
      |theta - phi| := by
  subst tau
  cases sigma <;>
    simp [signedRayDirection, angle_rayDirection theta phi hdiff,
      InnerProductGeometry.angle_neg_neg]

theorem angle_signedRayDirection_eq_pi_sub_of_sign_ne
    {sigma tau : Bool} {theta phi : ℝ}
    (hsign : sigma ≠ tau)
    (hdiff : |theta - phi| ≤ Real.pi) :
    InnerProductGeometry.angle
        (signedRayDirection sigma theta)
        (signedRayDirection tau phi) =
      Real.pi - |theta - phi| := by
  cases sigma <;> cases tau <;>
    simp_all [signedRayDirection, angle_rayDirection theta phi hdiff,
      InnerProductGeometry.angle_neg_left,
      InnerProductGeometry.angle_neg_right]

/-- Positive radial scaling does not alter the ray angle. -/
theorem angle_positive_smul_signedRay
    {rho eta : ℝ} (hrho : 0 < rho) (heta : 0 < eta)
    (sigma tau : Bool) (theta phi : ℝ) :
    InnerProductGeometry.angle
        (rho • signedRayDirection sigma theta)
        (eta • signedRayDirection tau phi) =
      InnerProductGeometry.angle
        (signedRayDirection sigma theta)
        (signedRayDirection tau phi) := by
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hrho,
      InnerProductGeometry.angle_smul_right_of_pos _ _ heta]

/-- Opposite canonical signs under the global cap consume at least one full
cap unit in projective parameter. -/
theorem lam_le_parameter_gap_of_opposite_signs
    {rho eta theta phi lam : ℝ}
    {sigma tau : Bool}
    (hrho : 0 < rho) (heta : 0 < eta)
    (horder : theta ≤ phi)
    (hspan : phi - theta ≤ Real.pi)
    (hsign : sigma ≠ tau)
    (hcap :
      InnerProductGeometry.angle
          (rho • signedRayDirection sigma theta)
          (eta • signedRayDirection tau phi)
        ≤ Real.pi - lam) :
    lam ≤ phi - theta := by
  have habs : |theta - phi| = phi - theta := by
    rw [abs_of_nonpos]
    · ring
    · linarith
  have hdiff : |theta - phi| ≤ Real.pi := by
    rw [habs]
    exact hspan
  rw [angle_positive_smul_signedRay hrho heta,
      angle_signedRayDirection_eq_pi_sub_of_sign_ne hsign hdiff,
      habs] at hcap
  linarith

/-- Normalized form with lambda = pi/t: opposite signs imply t*g >= 1. -/
theorem one_le_t_mul_normalized_gap_of_opposite_signs
    {rho eta theta phi lam t : ℝ}
    {sigma tau : Bool}
    (hrho : 0 < rho) (heta : 0 < eta)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (horder : theta ≤ phi)
    (hspan : phi - theta ≤ Real.pi)
    (hsign : sigma ≠ tau)
    (hcap :
      InnerProductGeometry.angle
          (rho • signedRayDirection sigma theta)
          (eta • signedRayDirection tau phi)
        ≤ Real.pi - lam) :
    1 ≤ t * ((phi - theta) / Real.pi) := by
  have hgap :=
    lam_le_parameter_gap_of_opposite_signs
      hrho heta horder hspan hsign hcap
  rw [hlam] at hgap
  have hpi : 0 < Real.pi := Real.pi_pos
  field_simp [ne_of_gt ht, ne_of_gt hpi] at hgap ⊢
  nlinarith

#print axioms angle_signedRayDirection_eq_of_sign_eq
#print axioms angle_signedRayDirection_eq_pi_sub_of_sign_ne
#print axioms lam_le_parameter_gap_of_opposite_signs
#print axioms one_le_t_mul_normalized_gap_of_opposite_signs

end JSP000404Research
