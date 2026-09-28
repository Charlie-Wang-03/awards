import JSP000404Research.SmallAngleOuterBounds
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-!
# Separation forced by the Hamiltonian residual

The two-small-matching reduction produces, after relabelling,

  angle(c,b,x) + angle(y,b,z) <= delta*lambda
  angle(b,c,y) + angle(x,c,z) <= delta*lambda.

Under the global cap, the first small angle forces angle(b,c,x) to be large,
and the second forces angle(c,b,y) to be large.  Applying the angle triangle
inequality along the three-ray paths c-x-z-y at b and b-y-z-x at c shows that

  angle(x,b,z) >= (1-2*delta)*lambda
  angle(y,c,z) >= (1-2*delta)*lambda.

This is a strict geometric refinement of the Hamiltonian-residual terminal.
It does not yet close that terminal.
-/

namespace JSP000404Research

open Real

theorem hamiltonian_residual_cross_separation
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {delta lam : ℝ}
    (hcap : AngleCap p lam)
    {b c x y z : V}
    (hbc : b ≠ c)
    (hbx : b ≠ x)
    (hby : b ≠ y)
    (hcx : c ≠ x)
    (hcy : c ≠ y)
    (hB :
      EuclideanGeometry.angle (p c) (p b) (p x) +
          EuclideanGeometry.angle (p y) (p b) (p z)
        ≤ delta * lam)
    (hC :
      EuclideanGeometry.angle (p b) (p c) (p y) +
          EuclideanGeometry.angle (p x) (p c) (p z)
        ≤ delta * lam) :
    (1 - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p x) (p b) (p z)
      ∧
    (1 - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p y) (p c) (p z) := by
  have hBsecond0 :
      0 ≤ EuclideanGeometry.angle (p y) (p b) (p z) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hCsecond0 :
      0 ≤ EuclideanGeometry.angle (p x) (p c) (p z) :=
    EuclideanGeometry.angle_nonneg _ _ _

  have hA :
      EuclideanGeometry.angle (p c) (p b) (p x)
        ≤ delta * lam := by
    linarith
  have hD :
      EuclideanGeometry.angle (p b) (p c) (p y)
        ≤ delta * lam := by
    linarith

  have hOuterAtB :
      (1 - delta) * lam ≤
        EuclideanGeometry.angle (p c) (p b) (p y) := by
    exact outer_angle_ge_one_sub_mul_of_small_under_AngleCap
      hp hcap
      hbc.symm hcy hby.symm
      hD

  have hOuterAtC :
      (1 - delta) * lam ≤
        EuclideanGeometry.angle (p b) (p c) (p x) := by
    exact outer_angle_ge_one_sub_mul_of_small_under_AngleCap
      hp hcap
      hbc hbx hcx
      hA

  have hPathB1 :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p b) (p c) (p x) (p y)
  have hPathB2 :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p b) (p x) (p z) (p y)
  have hzyB :
      EuclideanGeometry.angle (p z) (p b) (p y) =
        EuclideanGeometry.angle (p y) (p b) (p z) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hzyB] at hPathB2

  have hPathC1 :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p c) (p b) (p y) (p x)
  have hPathC2 :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p c) (p y) (p z) (p x)
  have hzxC :
      EuclideanGeometry.angle (p z) (p c) (p x) =
        EuclideanGeometry.angle (p x) (p c) (p z) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hzxC] at hPathC2

  constructor <;> nlinarith

#print axioms hamiltonian_residual_cross_separation

end JSP000404Research
