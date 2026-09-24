
import JSP000404Research.RightHalfPlaneArg
import Mathlib.Tactic

/-!
# Betweenness of generic-projection lifted edge angles

The generic projection sends every increasing edge into the same open
right half-plane after multiplication by projectionRotator.

For an increasing triple i<j<k,

  p(k)-p(i) = (p(j)-p(i)) + (p(k)-p(j)).

The rotation map is additive, so the rotated outer edge is the sum of the two
rotated consecutive edges.  RightHalfPlaneArg then implies that its argument,
and therefore its lifted angle, lies between the two consecutive lifted
angles.

This closes the betweenness field required by ForwardAngleLift.
-/

namespace JSP000404Research

open Real Complex

@[simp] theorem planeToComplex_add
    (x y : Plane) :
    planeToComplex (x + y) =
      planeToComplex x + planeToComplex y := by
  exact map_add planeToComplex x y

theorem rotatedPlane_add
    (a : ℝ) (x y : Plane) :
    rotatedPlane a (x + y) =
      rotatedPlane a x + rotatedPlane a y := by
  unfold rotatedPlane
  rw [planeToComplex_add]
  ring

/-- Lifted angle of a sum lies between lifted angles of the summands whenever
both rotated vectors have positive real part. -/
theorem projectionLiftedAngle_add_between
    {a : ℝ} {x y : Plane}
    (hx : 0 < (rotatedPlane a x).re)
    (hy : 0 < (rotatedPlane a y).re) :
    (projectionLiftedAngle a x ≤
        projectionLiftedAngle a (x + y) ∧
      projectionLiftedAngle a (x + y) ≤
        projectionLiftedAngle a y)
    ∨
    (projectionLiftedAngle a y ≤
        projectionLiftedAngle a (x + y) ∧
      projectionLiftedAngle a (x + y) ≤
        projectionLiftedAngle a x) := by
  have harg :=
    arg_add_between_of_re_pos hx hy
  rw [← rotatedPlane_add] at harg
  unfold projectionLiftedAngle
  rcases harg with h | h
  · left
    constructor <;> linarith
  · right
    constructor <;> linarith

/-- Edge-vector decomposition along an increasing triple. -/
theorem edgeVector_add
    {V : Type*}
    (p : V → Plane)
    (i j k : V) :
    (p j - p i) + (p k - p j) =
      p k - p i := by
  abel

/-- Main generic-projection triangle betweenness theorem. -/
theorem generic_projection_liftedAngle_between
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i j k : ProjectionOrdered V}
    (hij :
      @LT.lt (ProjectionOrdered V)
        (ProjectionOrdered.projectionLinearOrder hp) i j)
    (hjk :
      @LT.lt (ProjectionOrdered V)
        (ProjectionOrdered.projectionLinearOrder hp) j k) :
    (projectionLiftedAngle
        (genericProjectionSlope p)
        (p j.toOriginal - p i.toOriginal)
      ≤
      projectionLiftedAngle
        (genericProjectionSlope p)
        (p k.toOriginal - p i.toOriginal)
      ∧
      projectionLiftedAngle
        (genericProjectionSlope p)
        (p k.toOriginal - p i.toOriginal)
      ≤
      projectionLiftedAngle
        (genericProjectionSlope p)
        (p k.toOriginal - p j.toOriginal))
    ∨
    (projectionLiftedAngle
        (genericProjectionSlope p)
        (p k.toOriginal - p j.toOriginal)
      ≤
      projectionLiftedAngle
        (genericProjectionSlope p)
        (p k.toOriginal - p i.toOriginal)
      ∧
      projectionLiftedAngle
        (genericProjectionSlope p)
        (p k.toOriginal - p i.toOriginal)
      ≤
      projectionLiftedAngle
        (genericProjectionSlope p)
        (p j.toOriginal - p i.toOriginal)) := by
  let a := genericProjectionSlope p
  let x := p j.toOriginal - p i.toOriginal
  let y := p k.toOriginal - p j.toOriginal
  have hxi :
      0 < (rotatedPlane a x).re := by
    rw [rotatedPlane_re]
    have hproj :=
      ProjectionOrdered.projection_increment_pos hp hij
    simpa [a, x, sub_apply] using hproj
  have hyi :
      0 < (rotatedPlane a y).re := by
    rw [rotatedPlane_re]
    have hproj :=
      ProjectionOrdered.projection_increment_pos hp hjk
    simpa [a, y, sub_apply] using hproj
  have hbetween :=
    projectionLiftedAngle_add_between hxi hyi
  have hsum :
      x + y = p k.toOriginal - p i.toOriginal := by
    simpa [x, y] using
      edgeVector_add p
        i.toOriginal j.toOriginal k.toOriginal
  rw [hsum] at hbetween
  simpa [a, x, y] using hbetween

#print axioms rotatedPlane_add
#print axioms projectionLiftedAngle_add_between
#print axioms generic_projection_liftedAngle_between

end JSP000404Research
