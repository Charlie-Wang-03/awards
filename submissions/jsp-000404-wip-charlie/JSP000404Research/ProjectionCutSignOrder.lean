import JSP000404Research.ProjectionOrderCanonicalOrder
import JSP000404Research.ProjectionCanonicalRayBridge
import JSP000404Research.CutProjectiveBandPartition
import Mathlib.Tactic

/-!
# Generic projection cut sign equals order orientation

For a positive polar representation

  x = rho * rayDirection theta,   -pi < theta < pi,

the canonical signed projective sign is false when theta<0 and true otherwise.

For the explicit generic-projection order, an increasing edge i<j has
canonical sign true (because projection order agrees with CanonicalPointLt).
Hence its forward lifted angle cannot be negative.  Its canonical projective
theta lies below the distinguished projection cut, so the cut operation flips
the canonical sign and gives cutRaySign=false.

Reversing the edge flips cutRaySign.  Therefore

  i < j  -> cutRaySign(i,j)=false,
  j < i  -> cutRaySign(i,j)=true.

Thus the projection-cut sign is exactly the incoming/outgoing Boolean used by
the ordered band code.
-/

namespace JSP000404Research

theorem canonicalRayRep_sigma_eq_of_polar_window
    {x : Plane} {rho theta : ℝ}
    (hx : x ≠ 0)
    (hrho : 0 < rho)
    (hlo : -Real.pi < theta)
    (hhi : theta < Real.pi)
    (hrep : x = rho • rayDirection theta) :
    (canonicalRayRep x hx).sigma =
      if theta < 0 then false else true := by
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
    have hu :=
      canonical_signed_projective_unique
        hRrho hrho hR0 hRpi hphi0 hphipi heq
    simpa [R,hneg] using hu.2
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
    have hu :=
      canonical_signed_projective_unique
        hRrho hrho hR0 hRpi hphi0 hphipi heq
    simpa [R,hneg] using hu.2

namespace ProjectionOrdered

theorem raySign_true_of_projection_lt
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i j : ProjectionOrdered V}
    (hij :
      @LT.lt (ProjectionOrdered V)
        (projectionLinearOrder hp) i j) :
    raySignAt (reindexedPoint_injective hp)
        i (⟨j, ne_of_gt hij⟩ : OtherVertex i) = true := by
  have hcanonOrig :
      CanonicalPointLt p i.toOriginal j.toOriginal :=
    (projection_lt_iff_canonicalPointLt hp i j).1 hij
  have hcanon :
      CanonicalPointLt (reindexedPoint p) i j := by
    simpa [CanonicalPointLt,reindexedPoint,sub_apply] using hcanonOrig
  exact
    (raySign_true_iff_canonicalPointLt
      (reindexedPoint_injective hp) (ne_of_lt hij)).2 hcanon

theorem centreForwardLiftedAngle_nonneg_of_lt
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i j : ProjectionOrdered V}
    (hij :
      @LT.lt (ProjectionOrdered V)
        (projectionLinearOrder hp) i j) :
    0 ≤ centreForwardLiftedAngle hp i
      (⟨j, ne_of_gt hij⟩ : OtherVertex i) := by
  let theta :=
    projectionLiftedAngle
      (genericProjectionSlope p)
      (p j.toOriginal - p i.toOriginal)
  have hwindow :=
    generic_edge_liftedAngle_window hp hij
  have hrho :=
    generic_edge_liftedRho_pos hp hij
  have hrep0 :=
    projection_polar_repr
      (genericProjectionSlope p)
      (p j.toOriginal - p i.toOriginal)
  have hrep :
      reindexedPoint p j - reindexedPoint p i =
        projectionLiftedRho
            (genericProjectionSlope p)
            (p j.toOriginal - p i.toOriginal) •
          rayDirection theta := by
    simpa [theta,reindexedPoint] using hrep0
  have hx :
      reindexedPoint p j - reindexedPoint p i ≠ 0 :=
    displacement_ne_zero
      (reindexedPoint_injective hp)
      i (⟨j, ne_of_gt hij⟩ : OtherVertex i)
  have hsigma :=
    canonicalRayRep_sigma_eq_of_polar_window
      hx hrho hwindow.1 hwindow.2 hrep
  have hsign :=
    raySign_true_of_projection_lt hp hij
  have hsigmaTrue :
      (canonicalRayRep
        (reindexedPoint p j - reindexedPoint p i) hx).sigma = true := by
    simpa [raySignAt] using hsign
  by_contra hnot
  have hneg : theta < 0 := lt_of_not_ge hnot
  rw [hsigma, if_pos hneg] at hsigmaTrue
  simp at hsigmaTrue
  simpa [centreForwardLiftedAngle,hij,theta] using
    (le_of_not_gt hnot)

theorem cutRaySign_projectionCut_eq_false_of_lt
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i j : ProjectionOrdered V}
    (hij :
      @LT.lt (ProjectionOrdered V)
        (projectionLinearOrder hp) i j) :
    cutRaySign
      (reindexedPoint_injective hp)
      (projectionProjectiveCut p)
      i (⟨j, ne_of_gt hij⟩ : OtherVertex i) = false := by
  let r : OtherVertex i := ⟨j, ne_of_gt hij⟩
  have hforward :
      0 ≤ centreForwardLiftedAngle hp i r :=
    centreForwardLiftedAngle_nonneg_of_lt hp hij
  have hbelow :
      rayThetaAt (reindexedPoint_injective hp) i r <
        projectionProjectiveCut p :=
    (rayTheta_lt_projectionCut_iff_forward_nonneg hp i r).2 hforward
  have hsign :
      raySignAt (reindexedPoint_injective hp) i r = true :=
    raySign_true_of_projection_lt hp hij
  unfold cutRaySign
  rw [if_pos hbelow, hsign]
  rfl

theorem cutRaySign_projectionCut_eq_true_of_gt
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i j : ProjectionOrdered V}
    (hji :
      @LT.lt (ProjectionOrdered V)
        (projectionLinearOrder hp) j i) :
    cutRaySign
      (reindexedPoint_injective hp)
      (projectionProjectiveCut p)
      i (⟨j, ne_of_lt hji⟩ : OtherVertex i) = true := by
  have hforward :=
    cutRaySign_projectionCut_eq_false_of_lt
      hp hji
  have hrev :=
    cutRaySign_reverse_eq_not
      (reindexedPoint_injective hp)
      (projectionProjectiveCut p)
      (ne_of_lt hji)
  simpa [hforward] using hrev

#print axioms canonicalRayRep_sigma_eq_of_polar_window
#print axioms cutRaySign_projectionCut_eq_false_of_lt
#print axioms cutRaySign_projectionCut_eq_true_of_gt

end ProjectionOrdered
end JSP000404Research
