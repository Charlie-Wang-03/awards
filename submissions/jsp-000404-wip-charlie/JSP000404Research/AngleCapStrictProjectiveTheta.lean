import JSP000404Research.AngleCapNoncollinear
import JSP000404Research.SignedRayAngle
import JSP000404Research.CentreProjectiveCycle
import Mathlib.Tactic

/-!
# Genuine AngleCap makes canonical projective ray parameters injective

Two distinct original rays with exactly the same projective theta
have physical angle either 0 or pi, violating the positive
original-plane AngleCap. Thus neither coincident nor antipodal
projective ray directions can occur at an actual centre. This
cannot be inferred from injectivity of the planar point map alone.
-/

namespace JSP000404Research

/-- Canonical projective angle data around an original centre are injective
under a strictly positive global AngleCap. -/
theorem rayThetaAt_injective_of_AngleCap
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {lam : ℝ} (hcap : AngleCap p lam) (hlam : 0 < lam)
    (i : V) :
    Function.Injective (rayThetaAt hp i) := by
  intro j k htheta
  by_contra hne
  have hjkVal : j.1 ≠ k.1 := by
    intro h
    exact hne (Subtype.ext h)
  have hdist :
      projectiveRayDistance
        (rayThetaAt hp i j) (rayThetaAt hp i k) = 0 := by
    simp [projectiveRayDistance, htheta]
  have hsmall :
      projectiveRayDistance
        (rayThetaAt hp i j) (rayThetaAt hp i k) < lam := by
    rw [hdist]
    exact hlam
  have hangle :=
    actual_angle_eq_projective_of_projective_lt_lam
      hp hcap j k hne hsmall
  have hzero :
      EuclideanGeometry.angle (p j.1) (p i) (p k.1) = 0 := by
    simpa [hdist] using hangle
  have hpos :=
    angleCap_actual_angle_pos_of_distinct
      hp hcap hlam j.2 hjkVal k.2.symm
  linarith

/-- The canonical projective angle list of a centre cycle has no repeated
values, a stronger property than its existing nondecreasing-order witness. -/
theorem centreProjectiveCycle_angles_nodup_of_AngleCap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam : ℝ} (hcap : AngleCap p lam) (hlam : 0 < lam)
    (i : V) (C : CentreProjectiveCycle hp i) :
    C.angles.Nodup := by
  simpa [CentreProjectiveCycle.angles] using
    C.nodup.map (rayThetaAt_injective_of_AngleCap hp hcap hlam i)

#print axioms rayThetaAt_injective_of_AngleCap
#print axioms centreProjectiveCycle_angles_nodup_of_AngleCap

end JSP000404Research
