import JSP000404Research.SignedRayAngle
import JSP000404Research.SignedRayMonodromy
import JSP000404Research.CanonicalRayReversal
import Mathlib.Tactic

/-!
# Small same-sign projective gaps give small genuine angles

For an ordinary adjacent canonical ray pair, equal canonical signs make the
genuine Euclidean angle equal to the projective parameter gap.

For the cyclic wrap gap, the lifted first ray at theta_first+pi has flipped
canonical sign.  Hence a no-transition wrap step means

  sign(last) = !sign(first),

and again the genuine Euclidean angle equals the wrap projective gap.

Consequently, if such a gap has normalized scaled width at most delta under

  lambda = pi/t,

then its genuine angle is at most delta*lambda.

This is the concrete bridge needed in the four-centre sharp case: the unique
zero-quotient gap of a deficit-two/support-two outer centre has total scaled
width below delta and therefore cannot involve the sharp ray, whose outer
triangle angle is strictly larger than delta*lambda.
-/

namespace JSP000404Research

open Real

/-- Ordinary sorted same-sign gap: exact genuine angle formula. -/
theorem actual_angle_eq_ordinary_projective_gap_of_sign_eq
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V)
    {j k : OtherVertex i}
    (horder : rayThetaAt hp i j ≤ rayThetaAt hp i k)
    (hsign : raySignAt hp i j = raySignAt hp i k) :
    EuclideanGeometry.angle (p j.1) (p i) (p k.1) =
      rayThetaAt hp i k - rayThetaAt hp i j := by
  have hspan :
      rayThetaAt hp i k - rayThetaAt hp i j ≤ Real.pi := by
    have hj0 := rayThetaAt_nonneg hp i j
    have hkpi := rayThetaAt_lt_pi hp i k
    linarith [Real.pi_pos]
  have habs :
      |rayThetaAt hp i j - rayThetaAt hp i k| =
        rayThetaAt hp i k - rayThetaAt hp i j := by
    rw [abs_of_nonpos]
    · ring
    · linarith
  change
    InnerProductGeometry.angle
        (p j.1 - p i) (p k.1 - p i) =
      rayThetaAt hp i k - rayThetaAt hp i j
  rw [rayRepAt_eq hp i j, rayRepAt_eq hp i k,
      angle_positive_smul_signedRay
        (rayRhoAt_pos hp i j) (rayRhoAt_pos hp i k)]
  rw [angle_signedRayDirection_eq_of_sign_eq hsign]
  · exact habs
  · rw [habs]
    exact hspan

/-- Quantitative ordinary form. -/
theorem actual_angle_le_delta_lam_of_ordinary_same_sign_gap
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t lam delta : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    {j k : OtherVertex i}
    (horder : rayThetaAt hp i j ≤ rayThetaAt hp i k)
    (hsign : raySignAt hp i j = raySignAt hp i k)
    (hsmall :
      t * ((rayThetaAt hp i k - rayThetaAt hp i j) / Real.pi)
        ≤ delta) :
    EuclideanGeometry.angle (p j.1) (p i) (p k.1) ≤
      delta * lam := by
  rw [actual_angle_eq_ordinary_projective_gap_of_sign_eq
      hp i horder hsign, hlam]
  have hpi : 0 < Real.pi := Real.pi_pos
  have htne : t ≠ 0 := ne_of_gt ht
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  field_simp [htne, hpine] at hsmall ⊢
  nlinarith

/-- Exact genuine angle formula for a no-transition wrap gap. -/
theorem actual_angle_eq_wrap_projective_gap_of_lifted_sign_eq
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V)
    {first last : OtherVertex i}
    (horder :
      rayThetaAt hp i first ≤ rayThetaAt hp i last)
    (hsign :
      raySignAt hp i last = !raySignAt hp i first) :
    EuclideanGeometry.angle (p last.1) (p i) (p first.1) =
      rayThetaAt hp i first + Real.pi -
        rayThetaAt hp i last := by
  have hgap0 :
      0 ≤ rayThetaAt hp i first + Real.pi -
        rayThetaAt hp i last := by
    have hfirst0 := rayThetaAt_nonneg hp i first
    have hlastpi := rayThetaAt_lt_pi hp i last
    linarith
  have hgapPi :
      rayThetaAt hp i first + Real.pi -
        rayThetaAt hp i last ≤ Real.pi := by
    linarith
  have hfirstLift :
      p first.1 - p i =
        rayRhoAt hp i first •
          signedRayDirection (!raySignAt hp i first)
            (rayThetaAt hp i first + Real.pi) := by
    rw [rayRepAt_eq hp i first]
    rw [signedRayDirection_not_add_pi]
  change
    InnerProductGeometry.angle
        (p last.1 - p i) (p first.1 - p i) =
      rayThetaAt hp i first + Real.pi -
        rayThetaAt hp i last
  rw [rayRepAt_eq hp i last, hfirstLift,
      angle_positive_smul_signedRay
        (rayRhoAt_pos hp i last) (rayRhoAt_pos hp i first)]
  rw [hsign]
  have htheta :
      rayThetaAt hp i last ≤ rayThetaAt hp i first + Real.pi := by
    linarith
  have habs :
      |rayThetaAt hp i last -
          (rayThetaAt hp i first + Real.pi)| =
        rayThetaAt hp i first + Real.pi -
          rayThetaAt hp i last := by
    rw [abs_of_nonpos]
    · ring
    · linarith
  rw [angle_signedRayDirection_eq_of_sign_eq rfl]
  · exact habs
  · rw [habs]
    exact hgapPi

/-- Quantitative wrap form. -/
theorem actual_angle_le_delta_lam_of_wrap_same_sign_gap
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t lam delta : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    {first last : OtherVertex i}
    (horder :
      rayThetaAt hp i first ≤ rayThetaAt hp i last)
    (hsign :
      raySignAt hp i last = !raySignAt hp i first)
    (hsmall :
      t * ((rayThetaAt hp i first + Real.pi -
        rayThetaAt hp i last) / Real.pi) ≤ delta) :
    EuclideanGeometry.angle (p last.1) (p i) (p first.1) ≤
      delta * lam := by
  rw [actual_angle_eq_wrap_projective_gap_of_lifted_sign_eq
      hp i horder hsign, hlam]
  have hpi : 0 < Real.pi := Real.pi_pos
  have htne : t ≠ 0 := ne_of_gt ht
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  field_simp [htne, hpine] at hsmall ⊢
  nlinarith

#print axioms actual_angle_eq_ordinary_projective_gap_of_sign_eq
#print axioms actual_angle_le_delta_lam_of_ordinary_same_sign_gap
#print axioms actual_angle_eq_wrap_projective_gap_of_lifted_sign_eq
#print axioms actual_angle_le_delta_lam_of_wrap_same_sign_gap

end JSP000404Research
