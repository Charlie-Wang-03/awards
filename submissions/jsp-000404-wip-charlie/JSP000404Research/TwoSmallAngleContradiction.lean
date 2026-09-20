import JSP000404Research.SharpOuterAngles
import Mathlib.Tactic

/-!
# Triangle contradiction from two small outer angles

If two angles of a nondegenerate triangle are each at most delta*lambda with
delta<1/2, then the third angle is strictly larger than pi-lambda.  Under the
global Sendov cap angle <= pi-lambda this is impossible.

This is the final Euclidean arithmetic used in the support-two/support-two
branch of the four-centre terminal.
-/

namespace JSP000404Research

open Real

theorem third_angle_gt_pi_sub_lam_of_two_delta_small
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hdelta : delta < (1 : ℝ) / 2)
    (hlam : 0 < lam)
    {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha :
      EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam)
    (hb :
      EuclideanGeometry.angle (p a) (p b) (p c) ≤ delta * lam) :
    Real.pi - lam <
      EuclideanGeometry.angle (p a) (p c) (p b) := by
  have hsum :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p b) (p₂ := p a) (p c)
      (hp.ne hab.symm)
  have hcommA :
      EuclideanGeometry.angle (p c) (p a) (p b) =
        EuclideanGeometry.angle (p b) (p a) (p c) :=
    EuclideanGeometry.angle_comm _ _ _
  have hcommB :
      EuclideanGeometry.angle (p a) (p b) (p c) =
        EuclideanGeometry.angle (p c) (p b) (p a) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcommA] at hsum
  have hthirdComm :
      EuclideanGeometry.angle (p a) (p c) (p b) =
        EuclideanGeometry.angle (p b) (p c) (p a) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hthirdComm]
  nlinarith

theorem impossible_two_delta_small_angles_under_cap
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hdelta : delta < (1 : ℝ) / 2)
    (hlam : 0 < lam)
    {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha :
      EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam)
    (hb :
      EuclideanGeometry.angle (p a) (p b) (p c) ≤ delta * lam) :
    False := by
  have hgt :=
    third_angle_gt_pi_sub_lam_of_two_delta_small
      hp hdelta hlam hab hac hbc ha hb
  have hle :=
    hcap a c b hac hbc hab.symm
  linarith

#print axioms third_angle_gt_pi_sub_lam_of_two_delta_small
#print axioms impossible_two_delta_small_angles_under_cap

end JSP000404Research
