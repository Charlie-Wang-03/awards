
import JSP000404Research.ProjectionAngleBetweenness
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

/-!
# Polar reconstruction of the generic-projection lifted angle

Let q be the nonzero complex rotator and w=q*z.  Polar decomposition gives

  q = ||q|| exp(i arg q),
  w = ||w|| exp(i arg w).

Therefore

  z = w/q
    = (||w||/||q||) exp(i(arg w-arg q)).

For the generic projection construction, z is the complex encoding of the
original planar edge, and arg w-arg q is exactly projectionLiftedAngle.

This yields the positive radial factor and the exact planar representation
required by ForwardAngleLift.
-/

namespace JSP000404Research

open Real Complex

/-- Polar form of a complex quotient, with a deliberately unwrapped argument
difference. -/
theorem complex_div_eq_norm_div_mul_exp_arg_sub
    (w q : ℂ)
    (hq : q ≠ 0) :
    w / q =
      ((‖w‖ / ‖q‖ : ℝ) : ℂ) *
        Complex.exp ((w.arg - q.arg) * Complex.I) := by
  have hnormq : ‖q‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hq
  symm
  apply (eq_div_iff hq).2
  calc
    (((‖w‖ / ‖q‖ : ℝ) : ℂ) *
          Complex.exp ((w.arg - q.arg) * Complex.I)) * q
        =
      (((‖w‖ / ‖q‖ : ℝ) : ℂ) *
          Complex.exp ((w.arg - q.arg) * Complex.I)) *
        ((‖q‖ : ℂ) *
          Complex.exp (q.arg * Complex.I)) := by
            rw [Complex.norm_mul_exp_arg_mul_I]
    _ =
      (‖w‖ : ℂ) *
        (Complex.exp ((w.arg - q.arg) * Complex.I) *
          Complex.exp (q.arg * Complex.I)) := by
            have hnorm :
                (‖w‖ / ‖q‖) * ‖q‖ = ‖w‖ :=
              div_mul_cancel₀ ‖w‖ hnormq
            push_cast [hnorm]
            ring
    _ =
      (‖w‖ : ℂ) *
        Complex.exp (w.arg * Complex.I) := by
            rw [← Complex.exp_add]
            congr 2
            push_cast
            ring
    _ = w := Complex.norm_mul_exp_arg_mul_I w

noncomputable def projectionLiftedRho
    (a : ℝ) (x : Plane) : ℝ :=
  ‖rotatedPlane a x‖ / ‖projectionRotator a‖

theorem projectionLiftedRho_pos
    {a : ℝ} {x : Plane}
    (hpos : 0 < (rotatedPlane a x).re) :
    0 < projectionLiftedRho a x := by
  unfold projectionLiftedRho
  apply div_pos
  · exact norm_pos_iff.mpr
      (rotatedPlane_ne_zero_of_re_pos hpos)
  · exact norm_pos_iff.mpr
      (projectionRotator_ne_zero a)

theorem planeToComplex_eq_projection_polar
    {a : ℝ} (x : Plane) :
    planeToComplex x =
      (projectionLiftedRho a x : ℂ) *
        Complex.exp
          (projectionLiftedAngle a x * Complex.I) := by
  let q := projectionRotator a
  let w := rotatedPlane a x
  have hq : q ≠ 0 :=
    projectionRotator_ne_zero a
  have hz :
      planeToComplex x = w / q := by
    apply (eq_div_iff hq).2
    simp [w, q, rotatedPlane, mul_comm]
  rw [hz,
      complex_div_eq_norm_div_mul_exp_arg_sub w q hq]
  rfl

theorem planeToComplex_smul_rayDirection
    (rho theta : ℝ) :
    planeToComplex (rho • rayDirection theta) =
      (rho : ℂ) *
        Complex.exp (theta * Complex.I) := by
  rw [map_smul, planeToComplex_rayDirection,
      Complex.exp_mul_I]
  simp [smul_eq_mul]

/-- Exact planar reconstruction from the lifted polar data. -/
theorem projection_polar_repr
    (a : ℝ) (x : Plane) :
    x =
      projectionLiftedRho a x •
        rayDirection (projectionLiftedAngle a x) := by
  apply planeToComplex_injective
  rw [planeToComplex_eq_projection_polar,
      planeToComplex_smul_rayDirection]

/-- Generic increasing-edge radial factor is strictly positive. -/
theorem generic_edge_liftedRho_pos
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {u v : ProjectionOrdered V}
    (huv :
      @LT.lt (ProjectionOrdered V)
        (ProjectionOrdered.projectionLinearOrder hp) u v) :
    0 <
      projectionLiftedRho
        (genericProjectionSlope p)
        (p v.toOriginal - p u.toOriginal) := by
  apply projectionLiftedRho_pos
  rw [rotatedPlane_re]
  have hproj :=
    ProjectionOrdered.projection_increment_pos hp huv
  simpa [sub_apply] using hproj

#print axioms complex_div_eq_norm_div_mul_exp_arg_sub
#print axioms projectionLiftedRho_pos
#print axioms planeToComplex_eq_projection_polar
#print axioms projection_polar_repr
#print axioms generic_edge_liftedRho_pos

end JSP000404Research
