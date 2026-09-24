
import JSP000404Research.GenericForwardAngleLift
import JSP000404Research.CanonicalRayReversal
import Mathlib.Tactic

/-!
# Generic-projection lifted angles and canonical projective rays

The generic projection gives every increasing edge a lifted forward direction
theta in one common interval of length pi.  Because the projection rotator has
positive real part, the chosen interval base lies strictly between -pi and 0.
Hence every generic forward lifted angle lies in (-pi,pi).

For an angle theta in this window, its canonical projective parameter in
[0,pi) is simply

  theta + pi, if theta < 0,
  theta,      otherwise.

This file proves that this elementary canonicalization is exactly the existing
rayThetaAt parameter.

For a centre i and another vertex j:

* if i<j, compare the generic forward polar representation of p(j)-p(i)
  directly with canonicalRayRep;
* if j<i, apply the same direct comparison at j to p(i)-p(j), then use the
  already-proved reversal invariance rayThetaAt_reverse_eq.

Thus the global generic-projection direction system and the local canonical
projective cycles are now connected at the level of individual rays.
-/

namespace JSP000404Research

open Real

/-- Canonical representative modulo pi for an angle already known to lie in
(-pi,pi). -/
noncomputable def canonicalizeProjectiveAngle (theta : ℝ) : ℝ :=
  if theta < 0 then theta + Real.pi else theta

theorem projectionAngleBase_gt_neg_pi
    (a : ℝ) :
    -Real.pi < projectionAngleBase a := by
  have harg :
      -(Real.pi / 2) < (projectionRotator a).arg := by
    have habs :
        |(projectionRotator a).arg| < Real.pi / 2 := by
      exact Complex.abs_arg_lt_pi_div_two_iff.mpr
        (Or.inl (by simp [projectionRotator]))
    exact (by simpa [abs_lt] using habs).1
  unfold projectionAngleBase
  linarith

theorem projectionAngleBase_lt_zero
    (a : ℝ) :
    projectionAngleBase a < 0 := by
  have harg :
      (projectionRotator a).arg < Real.pi / 2 := by
    have habs :
        |(projectionRotator a).arg| < Real.pi / 2 := by
      exact Complex.abs_arg_lt_pi_div_two_iff.mpr
        (Or.inl (by simp [projectionRotator]))
    exact (by simpa [abs_lt] using habs).2
  unfold projectionAngleBase
  linarith

theorem generic_edge_liftedAngle_window
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {u v : ProjectionOrdered V}
    (huv :
      @LT.lt (ProjectionOrdered V)
        (ProjectionOrdered.projectionLinearOrder hp) u v) :
    -Real.pi <
      projectionLiftedAngle
        (genericProjectionSlope p)
        (p v.toOriginal - p u.toOriginal)
    ∧
    projectionLiftedAngle
        (genericProjectionSlope p)
        (p v.toOriginal - p u.toOriginal)
      < Real.pi := by
  have hmem := generic_edge_liftedAngle_mem hp huv
  have hbaseLo :=
    projectionAngleBase_gt_neg_pi
      (genericProjectionSlope p)
  have hbaseHi :=
    projectionAngleBase_lt_zero
      (genericProjectionSlope p)
  constructor <;> linarith

theorem canonicalizeProjectiveAngle_nonneg
    {theta : ℝ}
    (hlo : -Real.pi < theta) :
    0 ≤ canonicalizeProjectiveAngle theta := by
  unfold canonicalizeProjectiveAngle
  split_ifs with hneg
  · linarith
  · exact le_of_not_gt hneg

theorem canonicalizeProjectiveAngle_lt_pi
    {theta : ℝ}
    (hhi : theta < Real.pi) :
    canonicalizeProjectiveAngle theta < Real.pi := by
  unfold canonicalizeProjectiveAngle
  split_ifs with hneg
  · linarith [Real.pi_pos]
  · exact hhi

/-- A positive polar representation with theta in (-pi,pi) has canonical
projective parameter canonicalizeProjectiveAngle theta. -/
theorem canonicalRayRep_theta_eq_canonicalize_of_polar_window
    {x : Plane} {rho theta : ℝ}
    (hx : x ≠ 0)
    (hrho : 0 < rho)
    (hlo : -Real.pi < theta)
    (hhi : theta < Real.pi)
    (hrep :
      x = rho • rayDirection theta) :
    (canonicalRayRep x hx).theta =
      canonicalizeProjectiveAngle theta := by
  let R := canonicalRayRep x hx
  have hRrho : 0 < R.rho := R.rho_pos
  have hR0 : 0 ≤ R.theta := R.theta_nonneg
  have hRpi : R.theta < Real.pi := R.theta_lt_pi
  have hphi0 :
      0 ≤ canonicalizeProjectiveAngle theta :=
    canonicalizeProjectiveAngle_nonneg hlo
  have hphipi :
      canonicalizeProjectiveAngle theta < Real.pi :=
    canonicalizeProjectiveAngle_lt_pi hhi
  by_cases hneg : theta < 0
  · have hdir :
        signedRayDirection false
            (canonicalizeProjectiveAngle theta)
          =
        rayDirection theta := by
      rw [canonicalizeProjectiveAngle]
      simp only [if_pos hneg, signedRayDirection,
        Bool.false_eq_true, if_false]
      have hshift := rayDirection_add_pi theta
      rw [hshift]
      simp
    have heq :
        R.rho • signedRayDirection R.sigma R.theta =
          rho • signedRayDirection false
            (canonicalizeProjectiveAngle theta) := by
      rw [← R.eq_smul, hdir, ← hrep]
    exact
      (canonical_signed_projective_unique
        hRrho hrho hR0 hRpi hphi0 hphipi heq).1
  · have hdir :
        signedRayDirection true
            (canonicalizeProjectiveAngle theta)
          =
        rayDirection theta := by
      rw [canonicalizeProjectiveAngle]
      simp [hneg, signedRayDirection]
    have heq :
        R.rho • signedRayDirection R.sigma R.theta =
          rho • signedRayDirection true
            (canonicalizeProjectiveAngle theta) := by
      rw [← R.eq_smul, hdir, ← hrep]
    exact
      (canonical_signed_projective_unique
        hRrho hrho hR0 hRpi hphi0 hphipi heq).1

namespace ProjectionOrdered

/-- The lifted forward angle of the unoriented edge joining i to j, always
read in increasing generic-projection order. -/
noncomputable def centreForwardLiftedAngle
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    (j : OtherVertex i) : ℝ := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  exact if h : i < j.1 then
    projectionLiftedAngle
      (genericProjectionSlope p)
      (p j.1.toOriginal - p i.toOriginal)
  else
    projectionLiftedAngle
      (genericProjectionSlope p)
      (p i.toOriginal - p j.1.toOriginal)

/-- Every centre-forward lifted angle remains in the global (-pi,pi) window. -/
theorem centreForwardLiftedAngle_window
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    (j : OtherVertex i) :
    -Real.pi < centreForwardLiftedAngle hp i j ∧
      centreForwardLiftedAngle hp i j < Real.pi := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  unfold centreForwardLiftedAngle
  split_ifs with hij
  · exact generic_edge_liftedAngle_window hp hij
  · have hji : j.1 < i := by
      exact lt_of_le_of_ne
        (not_lt.mp hij)
        (Ne.symm j.2)
    exact generic_edge_liftedAngle_window hp hji

/-- Main individual-ray bridge: canonical projective theta is exactly the
pi-canonicalization of the generic projection's forward lifted angle. -/
theorem rayThetaAt_eq_canonicalize_centreForwardLiftedAngle
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    (j : OtherVertex i) :
    rayThetaAt
        (reindexedPoint_injective hp) i j
      =
    canonicalizeProjectiveAngle
      (centreForwardLiftedAngle hp i j) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let hp' : Function.Injective (reindexedPoint p) :=
    reindexedPoint_injective hp
  by_cases hij : i < j.1
  · have hwindow :=
      generic_edge_liftedAngle_window hp hij
    have hrho :=
      generic_edge_liftedRho_pos hp hij
    have hrepr :=
      projection_polar_repr
        (genericProjectionSlope p)
        (p j.1.toOriginal - p i.toOriginal)
    have htheta :
        rayThetaAt hp' i j =
          canonicalizeProjectiveAngle
            (projectionLiftedAngle
              (genericProjectionSlope p)
              (p j.1.toOriginal - p i.toOriginal)) := by
      change
        (canonicalRayRep
          (reindexedPoint p j.1 - reindexedPoint p i)
          (displacement_ne_zero hp' i j)).theta
          =
        canonicalizeProjectiveAngle
          (projectionLiftedAngle
            (genericProjectionSlope p)
            (p j.1.toOriginal - p i.toOriginal))
      apply canonicalRayRep_theta_eq_canonicalize_of_polar_window
        (displacement_ne_zero hp' i j)
        hrho hwindow.1 hwindow.2
      simpa [reindexedPoint] using hrepr
    simpa [centreForwardLiftedAngle, hij] using htheta
  · have hji : j.1 < i := by
      exact lt_of_le_of_ne
        (not_lt.mp hij)
        (Ne.symm j.2)
    let ji : OtherVertex j.1 := ⟨i, j.2⟩
    have hwindow :=
      generic_edge_liftedAngle_window hp hji
    have hrho :=
      generic_edge_liftedRho_pos hp hji
    have hrepr :=
      projection_polar_repr
        (genericProjectionSlope p)
        (p i.toOriginal - p j.1.toOriginal)
    have hthetaForward :
        rayThetaAt hp' j.1 ji =
          canonicalizeProjectiveAngle
            (projectionLiftedAngle
              (genericProjectionSlope p)
              (p i.toOriginal - p j.1.toOriginal)) := by
      change
        (canonicalRayRep
          (reindexedPoint p i - reindexedPoint p j.1)
          (displacement_ne_zero hp' j.1 ji)).theta
          =
        canonicalizeProjectiveAngle
          (projectionLiftedAngle
            (genericProjectionSlope p)
            (p i.toOriginal - p j.1.toOriginal))
      apply canonicalRayRep_theta_eq_canonicalize_of_polar_window
        (displacement_ne_zero hp' j.1 ji)
        hrho hwindow.1 hwindow.2
      simpa [reindexedPoint] using hrepr
    have hrev :
        rayThetaAt hp' i j =
          rayThetaAt hp' j.1 ji := by
      exact rayThetaAt_reverse_eq hp' j.2.symm
    rw [hrev, hthetaForward]
    simp [centreForwardLiftedAngle, hij]

#print axioms projectionAngleBase_gt_neg_pi
#print axioms projectionAngleBase_lt_zero
#print axioms generic_edge_liftedAngle_window
#print axioms canonicalRayRep_theta_eq_canonicalize_of_polar_window
#print axioms rayThetaAt_eq_canonicalize_centreForwardLiftedAngle

end ProjectionOrdered
end JSP000404Research
