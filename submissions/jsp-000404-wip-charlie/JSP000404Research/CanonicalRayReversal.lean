import JSP000404Research.SignedRayAngle
import JSP000404Research.FiniteProjectiveRays
import Mathlib.Tactic

/-!
# Uniqueness and reversal of canonical signed projective rays

Canonical projective parameters lie in the half-open strip

  rho > 0,  sigma : Bool,  0 <= theta < pi.

Within that strip the signed representation is unique in (sigma,theta).
Indeed, two positive-scaled representations of the same nonzero vector have
mutual angle zero.  Equal signs then force |theta-phi|=0; unequal signs would
force |theta-phi|=pi, impossible inside [0,pi).

Consequently the two orientations of one geometric edge have the same
projective parameter and opposite canonical signs.
-/

namespace JSP000404Research

open Real

theorem signedRayDirection_not_eq_neg
    (sigma : Bool) (theta : ℝ) :
    signedRayDirection (!sigma) theta =
      - signedRayDirection sigma theta := by
  cases sigma <;> simp [signedRayDirection]

theorem norm_signedRayDirection
    (sigma : Bool) (theta : ℝ) :
    ‖signedRayDirection sigma theta‖ = 1 := by
  cases sigma <;>
    simp [signedRayDirection, norm_rayDirection]

theorem signedRayDirection_ne_zero
    (sigma : Bool) (theta : ℝ) :
    signedRayDirection sigma theta ≠ 0 := by
  intro h
  have hn := congrArg norm h
  simp [norm_signedRayDirection] at hn

/-- Uniqueness of canonical sign and projective parameter. -/
theorem canonical_signed_projective_unique
    {rho eta theta phi : ℝ}
    {sigma tau : Bool}
    (hrho : 0 < rho) (heta : 0 < eta)
    (htheta0 : 0 ≤ theta) (hthetapi : theta < Real.pi)
    (hphi0 : 0 ≤ phi) (hphipi : phi < Real.pi)
    (heq :
      rho • signedRayDirection sigma theta =
        eta • signedRayDirection tau phi) :
    theta = phi ∧ sigma = tau := by
  have hleftne :
      rho • signedRayDirection sigma theta ≠ 0 := by
    exact smul_ne_zero ℝ (ne_of_gt hrho)
      (signedRayDirection_ne_zero sigma theta)
  have hang0 :
      InnerProductGeometry.angle
          (rho • signedRayDirection sigma theta)
          (eta • signedRayDirection tau phi) = 0 := by
    rw [← heq]
    exact InnerProductGeometry.angle_self hleftne
  rw [angle_positive_smul_signedRay hrho heta] at hang0
  have hdiffLt : |theta - phi| < Real.pi := by
    rw [abs_lt]
    constructor <;> linarith
  have hdiffLe : |theta - phi| ≤ Real.pi :=
    hdiffLt.le
  by_cases hsign : sigma = tau
  · have hangle :=
      angle_signedRayDirection_eq_of_sign_eq
        (theta := theta) (phi := phi) hsign hdiffLe
    rw [hangle] at hang0
    have htheta : theta = phi := by
      have : theta - phi = 0 := by
        exact abs_eq_zero.mp hang0
      linarith
    exact ⟨htheta, hsign⟩
  · have hangle :=
      angle_signedRayDirection_eq_pi_sub_of_sign_ne
        (theta := theta) (phi := phi) hsign hdiffLe
    rw [hangle] at hang0
    linarith

/-- Negating a canonical ray preserves theta and flips the sign. -/
theorem canonical_signed_projective_neg
    {rho eta theta phi : ℝ}
    {sigma tau : Bool}
    (hrho : 0 < rho) (heta : 0 < eta)
    (htheta0 : 0 ≤ theta) (hthetapi : theta < Real.pi)
    (hphi0 : 0 ≤ phi) (hphipi : phi < Real.pi)
    (heq :
      -(rho • signedRayDirection sigma theta) =
        eta • signedRayDirection tau phi) :
    theta = phi ∧ tau = !sigma := by
  have hrew :
      rho • signedRayDirection (!sigma) theta =
        eta • signedRayDirection tau phi := by
    rw [signedRayDirection_not_eq_neg]
    simpa [smul_neg] using heq
  have hu :=
    canonical_signed_projective_unique
      hrho heta htheta0 hthetapi hphi0 hphipi hrew
  exact ⟨hu.1, hu.2.symm⟩

/-- Canonical data at opposite orientations of one edge. -/
theorem rayThetaAt_reverse_eq_and_sign_not
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i j : V} (hij : i ≠ j) :
    rayThetaAt hp i ⟨j, hij.symm⟩ =
        rayThetaAt hp j ⟨i, hij⟩ ∧
      raySignAt hp j ⟨i, hij⟩ =
        ! raySignAt hp i ⟨j, hij.symm⟩ := by
  let ji : OtherVertex i := ⟨j, hij.symm⟩
  let ij : OtherVertex j := ⟨i, hij⟩
  have hforward := rayRepAt_eq hp i ji
  have hreverse := rayRepAt_eq hp j ij
  have hneg :
      -(p j - p i) = p i - p j := by
    abel
  have heq :
      -(rayRhoAt hp i ji •
          signedRayDirection
            (raySignAt hp i ji)
            (rayThetaAt hp i ji))
        =
      rayRhoAt hp j ij •
        signedRayDirection
          (raySignAt hp j ij)
          (rayThetaAt hp j ij) := by
    rw [← hforward, ← hreverse]
    exact hneg
  have hu :=
    canonical_signed_projective_neg
      (rayRhoAt_pos hp i ji)
      (rayRhoAt_pos hp j ij)
      (rayThetaAt_nonneg hp i ji)
      (rayThetaAt_lt_pi hp i ji)
      (rayThetaAt_nonneg hp j ij)
      (rayThetaAt_lt_pi hp j ij)
      heq
  exact ⟨hu.1, hu.2⟩

theorem rayThetaAt_reverse_eq
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i j : V} (hij : i ≠ j) :
    rayThetaAt hp i ⟨j, hij.symm⟩ =
      rayThetaAt hp j ⟨i, hij⟩ :=
  (rayThetaAt_reverse_eq_and_sign_not hp hij).1

theorem raySignAt_reverse_eq_not
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i j : V} (hij : i ≠ j) :
    raySignAt hp j ⟨i, hij⟩ =
      ! raySignAt hp i ⟨j, hij.symm⟩ :=
  (rayThetaAt_reverse_eq_and_sign_not hp hij).2

#print axioms canonical_signed_projective_unique
#print axioms canonical_signed_projective_neg
#print axioms rayThetaAt_reverse_eq
#print axioms raySignAt_reverse_eq_not

end JSP000404Research
