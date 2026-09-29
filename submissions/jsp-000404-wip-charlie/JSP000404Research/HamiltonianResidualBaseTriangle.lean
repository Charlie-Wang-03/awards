import JSP000404Research.HamiltonianResidualSeparation
import Mathlib.Tactic

/-!
# Base-triangle squeeze in the Hamiltonian residual terminal

For the Hamiltonian residual pattern

  angle(c,b,x) + angle(y,b,z) <= delta*lambda,
  angle(b,c,y) + angle(x,c,z) <= delta*lambda,

the global angle cap first forces the complementary angles
angle(c,b,y) and angle(b,c,x) to be at least (1-delta)*lambda.
The small residual terms then imply that both base angles of triangle b-c-z
are at least (1-2*delta)*lambda.  Consequently the angle at z is at most

  pi - 2*(1-2*delta)*lambda.

This is a source-independent planar consequence of the current hard terminal.
-/

namespace JSP000404Research

open Real

theorem hamiltonian_residual_base_triangle_bounds
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {delta lam : ℝ}
    (hcap : AngleCap p lam)
    {b c x y z : V}
    (hbc : b ≠ c)
    (hby : b ≠ y)
    (hcy : c ≠ y)
    (hbx : b ≠ x)
    (hcx : c ≠ x)
    (hbz : b ≠ z)
    (hcz : c ≠ z)
    (hB :
      EuclideanGeometry.angle (p c) (p b) (p x) +
          EuclideanGeometry.angle (p y) (p b) (p z)
        ≤ delta * lam)
    (hC :
      EuclideanGeometry.angle (p b) (p c) (p y) +
          EuclideanGeometry.angle (p x) (p c) (p z)
        ≤ delta * lam) :
    (1 - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p c) (p b) (p z)
      ∧
    (1 - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p b) (p c) (p z)
      ∧
    EuclideanGeometry.angle (p b) (p z) (p c)
      ≤ Real.pi - 2 * (1 - 2 * delta) * lam := by
  have hA0 :
      0 ≤ EuclideanGeometry.angle (p c) (p b) (p x) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hB0 :
      0 ≤ EuclideanGeometry.angle (p y) (p b) (p z) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hC0 :
      0 ≤ EuclideanGeometry.angle (p b) (p c) (p y) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hD0 :
      0 ≤ EuclideanGeometry.angle (p x) (p c) (p z) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hBsmall :
      EuclideanGeometry.angle (p y) (p b) (p z)
        ≤ delta * lam := by
    linarith
  have hDsmall :
      EuclideanGeometry.angle (p x) (p c) (p z)
        ≤ delta * lam := by
    linarith

  have hOuterB :
      (1 - delta) * lam ≤
        EuclideanGeometry.angle (p c) (p b) (p y) := by
    have hCsmall :
        EuclideanGeometry.angle (p b) (p c) (p y)
          ≤ delta * lam := by
      linarith
    exact outer_angle_ge_one_sub_mul_of_small_under_AngleCap
      hp hcap hbc.symm hcy hby hCsmall

  have hOuterC :
      (1 - delta) * lam ≤
        EuclideanGeometry.angle (p b) (p c) (p x) := by
    have hAsmall :
        EuclideanGeometry.angle (p c) (p b) (p x)
          ≤ delta * lam := by
      linarith
    exact outer_angle_ge_one_sub_mul_of_small_under_AngleCap
      hp hcap hbc hbx hcx hAsmall

  have hpathB :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p b) (p c) (p z) (p y)
  have hzyB :
      EuclideanGeometry.angle (p z) (p b) (p y) =
        EuclideanGeometry.angle (p y) (p b) (p z) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hzyB] at hpathB
  have hbaseB :
      (1 - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p c) (p b) (p z) := by
    nlinarith

  have hpathC :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p c) (p b) (p z) (p x)
  have hzxC :
      EuclideanGeometry.angle (p z) (p c) (p x) =
        EuclideanGeometry.angle (p x) (p c) (p z) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hzxC] at hpathC
  have hbaseC :
      (1 - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p b) (p c) (p z) := by
    nlinarith

  have hsum :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p c) (p₂ := p b) (p z)
      (hp.ne hbc)
  have hcommC :
      EuclideanGeometry.angle (p z) (p c) (p b) =
        EuclideanGeometry.angle (p b) (p c) (p z) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcommC] at hsum
  have hapex :
      EuclideanGeometry.angle (p b) (p z) (p c)
        ≤ Real.pi - 2 * (1 - 2 * delta) * lam := by
    nlinarith

  exact ⟨hbaseB, hbaseC, hapex⟩

#print axioms hamiltonian_residual_base_triangle_bounds

end JSP000404Research
