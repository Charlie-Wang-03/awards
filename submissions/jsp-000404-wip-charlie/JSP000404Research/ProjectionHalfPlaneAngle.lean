
import JSP000404Research.ProjectionOrderedVertices
import JSP000404Research.PlanarDirectionBridge
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Trigonometric
import Mathlib.Tactic

/-!
# A coherent angular branch from the generic projection half-plane

Encode a planar vector x=(x0,x1) by the complex number x0+i*x1.

For the generic projection slope a define

  q(a) = 1 - a*i.

Then

  Re(q(a) * (x0+i*x1)) = x0 + a*x1.

Hence every forward edge in the generic projection order is sent by q(a) into
the open right half-plane.

Its complex argument therefore lies strictly in (-pi/2,pi/2).  Subtracting
arg(q(a)) gives a coherent unwrapped direction parameter in the common
length-pi interval

  (-arg(q)-pi/2, -arg(q)+pi/2).

This file formalizes that common branch.  The remaining step to a complete
ForwardAngleLift is to reconstruct the original planar vector as a positive
multiple of rayDirection(theta), and to prove the triangle betweenness of
these theta values.
-/

namespace JSP000404Research

open Real Complex

noncomputable def planeToComplex (x : Plane) : ℂ :=
  ⟨x 0, x 1⟩

@[simp] theorem planeToComplex_re (x : Plane) :
    (planeToComplex x).re = x 0 := rfl

@[simp] theorem planeToComplex_im (x : Plane) :
    (planeToComplex x).im = x 1 := rfl

theorem planeToComplex_injective :
    Function.Injective planeToComplex := by
  intro x y h
  apply EuclideanSpace.ext
  intro i
  fin_cases i
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

@[simp] theorem planeToComplex_sub (x y : Plane) :
    planeToComplex (x - y) =
      planeToComplex x - planeToComplex y := by
  apply Complex.ext <;> rfl

noncomputable def projectionRotator (a : ℝ) : ℂ :=
  1 - a * Complex.I

@[simp] theorem projectionRotator_re (a : ℝ) :
    (projectionRotator a).re = 1 := by
  simp [projectionRotator]

@[simp] theorem projectionRotator_im (a : ℝ) :
    (projectionRotator a).im = -a := by
  simp [projectionRotator]

theorem projectionRotator_ne_zero (a : ℝ) :
    projectionRotator a ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [projectionRotator] at hre

noncomputable def rotatedPlane (a : ℝ) (x : Plane) : ℂ :=
  projectionRotator a * planeToComplex x

theorem rotatedPlane_re (a : ℝ) (x : Plane) :
    (rotatedPlane a x).re =
      x 0 + a * x 1 := by
  simp [rotatedPlane, projectionRotator, planeToComplex]
  ring

theorem rotatedPlane_im (a : ℝ) (x : Plane) :
    (rotatedPlane a x).im =
      x 1 - a * x 0 := by
  simp [rotatedPlane, projectionRotator, planeToComplex]
  ring

theorem rotatedPlane_ne_zero_of_re_pos
    {a : ℝ} {x : Plane}
    (hpos : 0 < (rotatedPlane a x).re) :
    rotatedPlane a x ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  linarith

/-- Right-half-plane arguments lie in the strict principal half interval. -/
theorem rotatedPlane_arg_mem_right_half
    {a : ℝ} {x : Plane}
    (hpos : 0 < (rotatedPlane a x).re) :
    -(Real.pi / 2) < (rotatedPlane a x).arg ∧
      (rotatedPlane a x).arg < Real.pi / 2 := by
  have habs :
      |(rotatedPlane a x).arg| < Real.pi / 2 := by
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr
      (Or.inl hpos)
  simpa [abs_lt] using habs

noncomputable def projectionAngleBase (a : ℝ) : ℝ :=
  -(projectionRotator a).arg - Real.pi / 2

noncomputable def projectionLiftedAngle
    (a : ℝ) (x : Plane) : ℝ :=
  (rotatedPlane a x).arg -
    (projectionRotator a).arg

theorem projectionLiftedAngle_lower
    {a : ℝ} {x : Plane}
    (hpos : 0 < (rotatedPlane a x).re) :
    projectionAngleBase a <
      projectionLiftedAngle a x := by
  have harg := (rotatedPlane_arg_mem_right_half hpos).1
  unfold projectionAngleBase projectionLiftedAngle
  linarith

theorem projectionLiftedAngle_upper
    {a : ℝ} {x : Plane}
    (hpos : 0 < (rotatedPlane a x).re) :
    projectionLiftedAngle a x <
      projectionAngleBase a + Real.pi := by
  have harg := (rotatedPlane_arg_mem_right_half hpos).2
  unfold projectionAngleBase projectionLiftedAngle
  linarith [Real.pi_pos]

/-- Generic-projection increasing edges all lie on this same angular branch. -/
theorem generic_edge_liftedAngle_mem
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {u v : ProjectionOrdered V}
    (huv :
      @LT.lt (ProjectionOrdered V)
        (ProjectionOrdered.projectionLinearOrder hp) u v) :
    projectionAngleBase (genericProjectionSlope p) <
      projectionLiftedAngle
        (genericProjectionSlope p)
        (p v.toOriginal - p u.toOriginal)
    ∧
    projectionLiftedAngle
        (genericProjectionSlope p)
        (p v.toOriginal - p u.toOriginal)
      <
      projectionAngleBase (genericProjectionSlope p) + Real.pi := by
  have hproj :=
    ProjectionOrdered.projection_increment_pos hp huv
  have hre :
      0 <
        (rotatedPlane
          (genericProjectionSlope p)
          (p v.toOriginal - p u.toOriginal)).re := by
    rw [rotatedPlane_re]
    simpa [sub_apply] using hproj
  exact ⟨projectionLiftedAngle_lower hre,
    projectionLiftedAngle_upper hre⟩

/-- The rotated edge itself has the standard positive polar representation. -/
theorem rotatedPlane_polar
    (a : ℝ) (x : Plane) :
    (‖rotatedPlane a x‖ : ℂ) *
        Complex.exp ((rotatedPlane a x).arg * Complex.I)
      =
    rotatedPlane a x := by
  exact Complex.norm_mul_exp_arg_mul_I _

#print axioms planeToComplex_injective
#print axioms rotatedPlane_re
#print axioms rotatedPlane_arg_mem_right_half
#print axioms generic_edge_liftedAngle_mem
#print axioms rotatedPlane_polar

end JSP000404Research
