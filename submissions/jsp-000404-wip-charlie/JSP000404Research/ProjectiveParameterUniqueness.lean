
import JSP000404Research.SignedRayAngle
import Mathlib.Tactic

/-!
# Uniqueness of the half-open projective angle parameter

Suppose a nonzero planar vector has two positive-radius signed-ray
representations

  x = rho * signedRayDirection sigma theta
  x = eta * signedRayDirection tau phi

with theta,phi both in [0,pi).

Then theta=phi.

Indeed the two represented vectors are identical, hence have angle zero.
Positive radial scaling does not change angle.  Equal signs give angle
|theta-phi|, while opposite signs give pi-|theta-phi|.  The latter cannot
vanish because two parameters in [0,pi) differ by strictly less than pi.

This theorem is the canonical uniqueness interface needed when comparing the
fixed [0,pi) projective cut with a generic-projection cut.
-/

namespace JSP000404Research

open Real

theorem rayDirection_ne_zero (theta : ℝ) :
    rayDirection theta ≠ 0 := by
  intro h
  have hn := congrArg norm h
  rw [norm_rayDirection] at hn
  simp at hn

theorem signedRayDirection_ne_zero
    (sigma : Bool) (theta : ℝ) :
    signedRayDirection sigma theta ≠ 0 := by
  cases sigma <;>
    simp [signedRayDirection, rayDirection_ne_zero theta]

theorem positive_smul_signedRay_ne_zero
    {rho : ℝ} (hrho : 0 < rho)
    (sigma : Bool) (theta : ℝ) :
    rho • signedRayDirection sigma theta ≠ 0 := by
  exact smul_ne_zero hrho.ne'
    (signedRayDirection_ne_zero sigma theta)

theorem projective_parameter_unique
    {x : Plane}
    {rho eta theta phi : ℝ}
    {sigma tau : Bool}
    (hrho : 0 < rho)
    (heta : 0 < eta)
    (htheta0 : 0 ≤ theta)
    (hthetaPi : theta < Real.pi)
    (hphi0 : 0 ≤ phi)
    (hphiPi : phi < Real.pi)
    (hxTheta :
      x = rho • signedRayDirection sigma theta)
    (hxPhi :
      x = eta • signedRayDirection tau phi) :
    theta = phi := by
  have hdiffLt :
      |theta - phi| < Real.pi := by
    rw [abs_lt]
    constructor <;> linarith
  have hdiff :
      |theta - phi| ≤ Real.pi :=
    hdiffLt.le
  have hx0 : x ≠ 0 := by
    rw [hxTheta]
    exact positive_smul_signedRay_ne_zero
      hrho sigma theta
  have hang :
      InnerProductGeometry.angle
          (signedRayDirection sigma theta)
          (signedRayDirection tau phi) = 0 := by
    have hscaled :
        InnerProductGeometry.angle
            (rho • signedRayDirection sigma theta)
            (eta • signedRayDirection tau phi) = 0 := by
      rw [← hxTheta, ← hxPhi]
      exact InnerProductGeometry.angle_self hx0
    rw [angle_positive_smul_signedRay
      hrho heta] at hscaled
    exact hscaled
  by_cases hsign : sigma = tau
  · rw [angle_signedRayDirection_eq_of_sign_eq
      hsign hdiff] at hang
    have hzero : theta - phi = 0 :=
      abs_eq_zero.mp hang
    linarith
  · rw [angle_signedRayDirection_eq_pi_sub_of_sign_ne
      hsign hdiff] at hang
    linarith

/-- Any admissible half-open projective representation recovers the canonical
rayThetaAt parameter. -/
theorem rayThetaAt_eq_of_projective_representation
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (j : OtherVertex i)
    {rho theta : ℝ} {sigma : Bool}
    (hrho : 0 < rho)
    (htheta0 : 0 ≤ theta)
    (hthetaPi : theta < Real.pi)
    (hrepr :
      p j.1 - p i =
        rho • signedRayDirection sigma theta) :
    rayThetaAt hp i j = theta := by
  apply projective_parameter_unique
    (rayRhoAt_pos hp i j) hrho
    (rayThetaAt_nonneg hp i j)
    (rayThetaAt_lt_pi hp i j)
    htheta0 hthetaPi
    (rayRepAt_eq hp i j)
    hrepr

#print axioms rayDirection_ne_zero
#print axioms signedRayDirection_ne_zero
#print axioms projective_parameter_unique
#print axioms rayThetaAt_eq_of_projective_representation

end JSP000404Research
