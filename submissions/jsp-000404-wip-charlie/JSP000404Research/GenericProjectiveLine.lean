
import JSP000404Research.GenericForwardAngleLift
import JSP000404Research.ProjectiveParameterUniqueness
import JSP000404Research.TransitionRotation
import Mathlib.Tactic

/-!
# Generic forward directions as projective line parameters

The generic projection gives an oriented angle for every increasing edge in
one common interval (base,base+pi).

For an unordered pair i!=j, use the increasing orientation to define its
generic line angle.  Relative to a chosen centre, the displacement to the
other endpoint is either the positive ray at that angle or its negative, so
the same angle is a valid signed projective parameter.

The rotator q=1-a*i has positive real part.  Hence its argument belongs to
(-pi/2,pi/2), which implies

  -pi < base < 0 < base+pi < pi.

Therefore a generic line angle is already in (-pi,pi).  Its canonical
projective representative in [0,pi) is obtained by the single cut change

  theta          if 0 <= theta,
  theta + pi     if theta < 0.

This is the pointwise bridge between the generic-projection cut and the
canonical projective cut.
-/

namespace JSP000404Research

open Real Complex

theorem projectionAngleBase_neg
    (a : ℝ) :
    projectionAngleBase a < 0 := by
  have harg :
      -(Real.pi / 2) < (projectionRotator a).arg ∧
        (projectionRotator a).arg < Real.pi / 2 := by
    have habs :
        |(projectionRotator a).arg| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr
        (Or.inl (by simp [projectionRotator]))
    simpa [abs_lt] using habs
  unfold projectionAngleBase
  linarith

theorem neg_pi_lt_projectionAngleBase
    (a : ℝ) :
    -Real.pi < projectionAngleBase a := by
  have harg :
      -(Real.pi / 2) < (projectionRotator a).arg ∧
        (projectionRotator a).arg < Real.pi / 2 := by
    have habs :
        |(projectionRotator a).arg| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr
        (Or.inl (by simp [projectionRotator]))
    simpa [abs_lt] using habs
  unfold projectionAngleBase
  linarith

theorem projectionAngleBase_add_pi_pos
    (a : ℝ) :
    0 < projectionAngleBase a + Real.pi := by
  linarith [neg_pi_lt_projectionAngleBase a]

theorem projectionAngleBase_add_pi_lt_pi
    (a : ℝ) :
    projectionAngleBase a + Real.pi < Real.pi := by
  linarith [projectionAngleBase_neg a]

namespace ProjectionOrdered

noncomputable def genericLineAngle
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i j : ProjectionOrdered V) : ℝ :=
  if h :
      @LT.lt (ProjectionOrdered V)
        (projectionLinearOrder hp) i j then
    projectionLiftedAngle
      (genericProjectionSlope p)
      (p j.toOriginal - p i.toOriginal)
  else
    projectionLiftedAngle
      (genericProjectionSlope p)
      (p i.toOriginal - p j.toOriginal)

/-- Every unordered generic line angle lies in the common width-pi branch. -/
theorem genericLineAngle_mem
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i j : ProjectionOrdered V}
    (hij : i ≠ j) :
    projectionAngleBase (genericProjectionSlope p) <
      genericLineAngle hp i j
    ∧
    genericLineAngle hp i j <
      projectionAngleBase (genericProjectionSlope p) + Real.pi := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · simp only [genericLineAngle, if_pos hijlt]
    exact generic_edge_liftedAngle_mem hp hijlt
  · have hnot : ¬ i < j := not_lt_of_ge hjilt.le
    simp only [genericLineAngle, if_neg hnot]
    exact generic_edge_liftedAngle_mem hp hjilt

/-- The centre-to-neighbour displacement has a positive-radius signed
representation using the generic line angle. -/
theorem genericLineAngle_projective_representation
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i j : ProjectionOrdered V}
    (hij : i ≠ j) :
    ∃ rho : ℝ, ∃ sigma : Bool,
      0 < rho ∧
      p j.toOriginal - p i.toOriginal =
        rho • signedRayDirection sigma
          (genericLineAngle hp i j) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · let x := p j.toOriginal - p i.toOriginal
    let a := genericProjectionSlope p
    refine ⟨projectionLiftedRho a x, true, ?_, ?_⟩
    · exact generic_edge_liftedRho_pos hp hijlt
    · have hrepr := projection_polar_repr a x
      simpa [genericLineAngle, hijlt,
        signedRayDirection, a, x] using hrepr
  · have hnot : ¬ i < j := not_lt_of_ge hjilt.le
    let x := p i.toOriginal - p j.toOriginal
    let a := genericProjectionSlope p
    refine ⟨projectionLiftedRho a x, false, ?_, ?_⟩
    · exact generic_edge_liftedRho_pos hp hjilt
    · have hrepr := projection_polar_repr a x
      have hneg :
          p j.toOriginal - p i.toOriginal = -x := by
        dsimp [x]
        abel
      rw [hneg, hrepr]
      simp [genericLineAngle, hnot,
        signedRayDirection, a, x]

/-- If the generic line angle is nonnegative, it is already the canonical
[0,pi) projective parameter. -/
theorem canonicalTheta_eq_genericLineAngle_of_nonneg
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    (j : OtherVertex i.toOriginal)
    (hTheta :
      0 ≤
        genericLineAngle hp i
          (ofOriginal j.1)) :
    rayThetaAt hp i.toOriginal j =
      genericLineAngle hp i (ofOriginal j.1) := by
  have hij :
      i ≠ ofOriginal j.1 := by
    intro h
    apply j.2
    exact congrArg toOriginal h |>.symm
  have hmem := genericLineAngle_mem hp hij
  have hpi :
      genericLineAngle hp i (ofOriginal j.1) < Real.pi := by
    exact hmem.2.trans
      (projectionAngleBase_add_pi_lt_pi
        (genericProjectionSlope p))
  obtain ⟨rho, sigma, hrho, hrepr⟩ :=
    genericLineAngle_projective_representation hp hij
  exact rayThetaAt_eq_of_projective_representation
    hp i.toOriginal j
    hrho hTheta hpi hrepr

/-- If the generic line angle is negative, adding pi gives the canonical
[0,pi) projective parameter. -/
theorem canonicalTheta_eq_genericLineAngle_add_pi_of_neg
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    (j : OtherVertex i.toOriginal)
    (hTheta :
      genericLineAngle hp i
        (ofOriginal j.1) < 0) :
    rayThetaAt hp i.toOriginal j =
      genericLineAngle hp i (ofOriginal j.1) + Real.pi := by
  have hij :
      i ≠ ofOriginal j.1 := by
    intro h
    apply j.2
    exact congrArg toOriginal h |>.symm
  have hmem := genericLineAngle_mem hp hij
  have h0 :
      0 ≤ genericLineAngle hp i
          (ofOriginal j.1) + Real.pi := by
    have hbase :=
      neg_pi_lt_projectionAngleBase
        (genericProjectionSlope p)
    linarith
  have hpi :
      genericLineAngle hp i
          (ofOriginal j.1) + Real.pi < Real.pi := by
    linarith
  obtain ⟨rho, sigma, hrho, hrepr⟩ :=
    genericLineAngle_projective_representation hp hij
  have hrepr' :
      p j.1 - p i.toOriginal =
        rho • signedRayDirection (!sigma)
          (genericLineAngle hp i
            (ofOriginal j.1) + Real.pi) := by
    rw [← same_ray_after_pi_shift_to_common_sign
      sigma
      (genericLineAngle hp i
        (ofOriginal j.1))]
    exact hrepr
  exact rayThetaAt_eq_of_projective_representation
    hp i.toOriginal j
    hrho h0 hpi hrepr'

#print axioms projectionAngleBase_neg
#print axioms neg_pi_lt_projectionAngleBase
#print axioms genericLineAngle_mem
#print axioms genericLineAngle_projective_representation
#print axioms canonicalTheta_eq_genericLineAngle_of_nonneg
#print axioms canonicalTheta_eq_genericLineAngle_add_pi_of_neg

end ProjectionOrdered
end JSP000404Research
