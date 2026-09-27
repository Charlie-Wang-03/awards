import JSP000404Research.TwoSmallAngleContradiction
import Mathlib.Tactic

/-!
# Triangle contradiction from two differently scaled small angles

The existing TwoSmallAngleContradiction uses the same coefficient delta at
both vertices.  For mixed support types we need the asymmetric form.

If two angles in a nondegenerate triangle are bounded by

  alpha * lambda,  beta * lambda

with alpha+beta<1, then the third angle is strictly larger than pi-lambda,
contradicting AngleCap.
-/

namespace JSP000404Research

open Real

theorem third_angle_gt_pi_sub_lam_of_two_scaled_small
    {V : Type*} {p : V → Plane}
    {alpha beta lam : ℝ}
    (hp : Function.Injective p)
    (hsumCoeff : alpha + beta < 1)
    (hlam : 0 < lam)
    {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha :
      EuclideanGeometry.angle (p b) (p a) (p c) ≤ alpha * lam)
    (hb :
      EuclideanGeometry.angle (p a) (p b) (p c) ≤ beta * lam) :
    Real.pi - lam <
      EuclideanGeometry.angle (p a) (p c) (p b) := by
  have htri :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p b) (p₂ := p a) (p c)
      (hp.ne hab.symm)
  have hcommA :
      EuclideanGeometry.angle (p c) (p a) (p b) =
        EuclideanGeometry.angle (p b) (p a) (p c) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcommA] at htri
  have hthird :
      EuclideanGeometry.angle (p a) (p c) (p b) =
        EuclideanGeometry.angle (p b) (p c) (p a) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hthird]
  nlinarith

theorem impossible_two_scaled_small_angles_under_cap
    {V : Type*} {p : V → Plane}
    {alpha beta lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hsumCoeff : alpha + beta < 1)
    (hlam : 0 < lam)
    {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha :
      EuclideanGeometry.angle (p b) (p a) (p c) ≤ alpha * lam)
    (hb :
      EuclideanGeometry.angle (p a) (p b) (p c) ≤ beta * lam) :
    False := by
  have hgt :=
    third_angle_gt_pi_sub_lam_of_two_scaled_small
      hp hsumCoeff hlam hab hac hbc ha hb
  have hle :=
    hcap a c b hac hbc hab.symm
  linarith

theorem support_two_coeff_lt_half
    {delta : ℝ}
    (hdeltaHalf : delta < (1 : ℝ) / 2) :
    (1 + delta) / 3 < (1 : ℝ) / 2 := by
  linarith

theorem two_support_two_coeff_sum_lt_one
    {delta : ℝ}
    (hdeltaHalf : delta < (1 : ℝ) / 2) :
    (1 + delta) / 3 + (1 + delta) / 3 < (1 : ℝ) := by
  linarith

theorem support_two_three_coeff_sum_lt_one
    {delta : ℝ}
    (hdeltaHalf : delta < (1 : ℝ) / 2) :
    (1 + delta) / 3 + delta < (1 : ℝ) := by
  linarith

#print axioms impossible_two_scaled_small_angles_under_cap
#print axioms two_support_two_coeff_sum_lt_one
#print axioms support_two_three_coeff_sum_lt_one

end JSP000404Research
