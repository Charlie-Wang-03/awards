import JSP000404Research.SharpCentre
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-!
# Outer-angle bounds from one small angle under the global cap

If one angle of a nondegenerate triangle is at most alpha*lambda and every
angle is globally at most pi-lambda, then each of the other two angles is at
least (1-alpha)*lambda.

Unlike SharpOuterAngles, this theorem needs only one explicit small-angle
hypothesis; the small-angle vertex need not be globally SharpAt.
-/

namespace JSP000404Research

open Real

theorem outer_angle_ge_one_sub_mul_of_small_and_cap
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {alpha lam : ℝ}
    {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsmall :
      EuclideanGeometry.angle (p b) (p a) (p c) ≤
        alpha * lam)
    (hcapC :
      EuclideanGeometry.angle (p a) (p c) (p b) ≤
        Real.pi - lam) :
    (1 - alpha) * lam ≤
      EuclideanGeometry.angle (p a) (p b) (p c) := by
  have hsum :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p b) (p₂ := p a) (p c)
      (hp.ne hab)
  have hcomm :
      EuclideanGeometry.angle (p c) (p b) (p a) =
        EuclideanGeometry.angle (p a) (p b) (p c) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcomm] at hsum
  nlinarith

theorem outer_angle_ge_one_sub_mul_of_small_under_AngleCap
    {V : Type*} {p : V → Plane}
    {alpha lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsmall :
      EuclideanGeometry.angle (p b) (p a) (p c) ≤
        alpha * lam) :
    (1 - alpha) * lam ≤
      EuclideanGeometry.angle (p a) (p b) (p c) := by
  apply outer_angle_ge_one_sub_mul_of_small_and_cap
    hp hab hac hbc hsmall
  exact hcap a c b hac hab hbc.symm

/-- Both non-small vertices receive the same lower bound. -/
theorem both_outer_angles_ge_one_sub_mul_of_small_under_AngleCap
    {V : Type*} {p : V → Plane}
    {alpha lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsmall :
      EuclideanGeometry.angle (p b) (p a) (p c) ≤
        alpha * lam) :
    (1 - alpha) * lam ≤
        EuclideanGeometry.angle (p a) (p b) (p c)
      ∧
    (1 - alpha) * lam ≤
        EuclideanGeometry.angle (p a) (p c) (p b) := by
  constructor
  · exact outer_angle_ge_one_sub_mul_of_small_under_AngleCap
      hp hcap hab hac hbc hsmall
  · have hsmall' :
        EuclideanGeometry.angle (p c) (p a) (p b) ≤
          alpha * lam := by
      rw [EuclideanGeometry.angle_comm]
      exact hsmall
    exact outer_angle_ge_one_sub_mul_of_small_under_AngleCap
      hp hcap hac hab hbc.symm hsmall'

#print axioms outer_angle_ge_one_sub_mul_of_small_and_cap
#print axioms outer_angle_ge_one_sub_mul_of_small_under_AngleCap
#print axioms both_outer_angles_ge_one_sub_mul_of_small_under_AngleCap

end JSP000404Research
