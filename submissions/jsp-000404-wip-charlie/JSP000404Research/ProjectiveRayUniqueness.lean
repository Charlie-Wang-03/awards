
import JSP000404Research.SignedRayAngle
import Mathlib.Tactic

/-!
# Uniqueness of the canonical projective angle

A nonzero planar vector may have two signed representations

  rho * signedRayDirection sigma theta
  eta * signedRayDirection tau phi,

with positive radii and theta,phi in the canonical half-open interval [0,pi).

The projective angle is nevertheless unique: theta=phi.

First, every signedRayDirection has norm one, so equality of the represented
vectors forces rho=eta.  Cancelling the common positive scalar leaves equality
of the signed unit directions.

If the signs agree, their angle is |theta-phi|, hence theta=phi.
If the signs differ, their angle is pi-|theta-phi|.  Equality of the unit
directions would force |theta-phi|=pi, impossible for two parameters in
[0,pi).

This makes the chosen canonical rayThetaAt observationally unique and allows
other positive signed representations to be identified with it.
-/

namespace JSP000404Research

open Real

@[simp] theorem norm_signedRayDirection
    (sigma : Bool) (theta : ℝ) :
    ‖signedRayDirection sigma theta‖ = 1 := by
  cases sigma <;>
    simp [signedRayDirection, norm_rayDirection]

theorem signedRayDirection_ne_zero
    (sigma : Bool) (theta : ℝ) :
    signedRayDirection sigma theta ≠ 0 := by
  intro h
  have hn := congrArg norm h
  simpa using hn

/-- Two positive signed representations in the canonical projective interval
have the same projective angle. -/
theorem projective_theta_unique_of_positive_signed_repr
    {rho eta theta phi : ℝ}
    {sigma tau : Bool}
    (hrho : 0 < rho)
    (heta : 0 < eta)
    (htheta0 : 0 ≤ theta)
    (hthetaPi : theta < Real.pi)
    (hphi0 : 0 ≤ phi)
    (hphiPi : phi < Real.pi)
    (heq :
      rho • signedRayDirection sigma theta =
        eta • signedRayDirection tau phi) :
    theta = phi := by
  have hnorm := congrArg norm heq
  have hrhoEq : rho = eta := by
    simpa [norm_smul, norm_signedRayDirection,
      Real.norm_eq_abs, abs_of_pos hrho,
      abs_of_pos heta] using hnorm
  subst eta
  have hdir :
      signedRayDirection sigma theta =
        signedRayDirection tau phi := by
    exact (smul_right_injective Plane hrho.ne').eq_iff.mp heq
  have hangleZero :
      InnerProductGeometry.angle
          (signedRayDirection sigma theta)
          (signedRayDirection tau phi) = 0 := by
    rw [hdir]
    exact InnerProductGeometry.angle_self
      (signedRayDirection_ne_zero tau phi)
  have hdiff :
      |theta - phi| < Real.pi := by
    rw [abs_lt]
    constructor <;> linarith
  have hdiffLe :
      |theta - phi| ≤ Real.pi :=
    hdiff.le
  by_cases hsign : sigma = tau
  · have hang :=
      angle_signedRayDirection_eq_of_sign_eq
        hsign hdiffLe
    rw [hangleZero] at hang
    have hz : theta - phi = 0 := by
      exact abs_eq_zero.mp hang.symm
    linarith
  · have hang :=
      angle_signedRayDirection_eq_pi_sub_of_sign_ne
        hsign hdiffLe
    rw [hangleZero] at hang
    have hpiEq :
        |theta - phi| = Real.pi := by
      linarith
    linarith

/-- Any positive canonical-interval representation of a displacement has the
same theta as rayThetaAt. -/
theorem rayThetaAt_eq_of_positive_signed_repr
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
  apply projective_theta_unique_of_positive_signed_repr
    (rayRhoAt_pos hp i j) hrho
    (rayThetaAt_nonneg hp i j)
    (rayThetaAt_lt_pi hp i j)
    htheta0 hthetaPi
  rw [← rayRepAt_eq hp i j, ← hrepr]

#print axioms norm_signedRayDirection
#print axioms projective_theta_unique_of_positive_signed_repr
#print axioms rayThetaAt_eq_of_positive_signed_repr

end JSP000404Research
