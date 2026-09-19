import JSP000404Research.ProjectiveInterval
import Mathlib.Tactic

/-!
# Opposite projective-ray signs require one full cap unit

Represent planar rays by signed projective directions

  signedRayDirection sigma theta.

If two signs are opposite, their genuine Euclidean angle is the supplement of
the underlying projective-direction angle.  Hence, under the global angle cap

  angle <= pi - lam,

opposite signs force projective separation at least lam.

Consequently any projective gap shorter than lam has equal signs at its two
endpoints.  In Sendov-normalized units this says: every quotient-zero gap
preserves the orientation sign.
-/

namespace JSP000404Research

open Real

/-- Opposite signs turn projective separation into a supplementary angle. -/
theorem angle_signedRay_of_sign_ne
    {theta phi : ℝ}
    (hdiff : |theta - phi| ≤ Real.pi)
    {sigma tau : Bool}
    (hsign : sigma ≠ tau) :
    InnerProductGeometry.angle
        (signedRayDirection sigma theta)
        (signedRayDirection tau phi)
      = Real.pi - |theta - phi| := by
  have hang := angle_rayDirection theta phi hdiff
  cases sigma <;> cases tau
  · simp at hsign
  · change InnerProductGeometry.angle
      (-rayDirection theta) (rayDirection phi) =
        Real.pi - |theta - phi|
    rw [InnerProductGeometry.angle_neg_left, hang]
  · change InnerProductGeometry.angle
      (rayDirection theta) (-rayDirection phi) =
        Real.pi - |theta - phi|
    rw [InnerProductGeometry.angle_neg_right, hang]
  · simp at hsign

/-- Under an angle cap pi-lam, opposite signed rays must be projectively
separated by at least lam. -/
theorem projective_separation_ge_of_sign_ne_of_cap
    {theta phi lam : ℝ}
    (hdiff : |theta - phi| ≤ Real.pi)
    {sigma tau : Bool}
    (hsign : sigma ≠ tau)
    (hcap :
      InnerProductGeometry.angle
          (signedRayDirection sigma theta)
          (signedRayDirection tau phi)
        ≤ Real.pi - lam) :
    lam ≤ |theta - phi| := by
  rw [angle_signedRay_of_sign_ne hdiff hsign] at hcap
  linarith

/-- Equivalently, any projective gap shorter than one cap unit has equal
orientation signs. -/
theorem sign_eq_of_projective_separation_lt_cap
    {theta phi lam : ℝ}
    (hdiffPi : |theta - phi| ≤ Real.pi)
    {sigma tau : Bool}
    (hsmall : |theta - phi| < lam)
    (hcap :
      InnerProductGeometry.angle
          (signedRayDirection sigma theta)
          (signedRayDirection tau phi)
        ≤ Real.pi - lam) :
    sigma = tau := by
  by_contra hsign
  have hsep :=
    projective_separation_ge_of_sign_ne_of_cap
      hdiffPi hsign hcap
  linarith

/-- Normalized form: if gap = x*lam with 0 <= x < 1 and lam>0, opposite
signs are impossible under the same angle cap. -/
theorem sign_eq_of_normalized_gap_lt_one
    {theta phi x lam : ℝ}
    (hlam : 0 < lam)
    (hgap : |theta - phi| = x * lam)
    (hx0 : 0 ≤ x)
    (hx1 : x < 1)
    (hdiffPi : |theta - phi| ≤ Real.pi)
    {sigma tau : Bool}
    (hcap :
      InnerProductGeometry.angle
          (signedRayDirection sigma theta)
          (signedRayDirection tau phi)
        ≤ Real.pi - lam) :
    sigma = tau := by
  apply sign_eq_of_projective_separation_lt_cap hdiffPi
  · rw [hgap]
    nlinarith
  · exact hcap

#print axioms angle_signedRay_of_sign_ne
#print axioms projective_separation_ge_of_sign_ne_of_cap
#print axioms sign_eq_of_projective_separation_lt_cap
#print axioms sign_eq_of_normalized_gap_lt_one

end JSP000404Research
