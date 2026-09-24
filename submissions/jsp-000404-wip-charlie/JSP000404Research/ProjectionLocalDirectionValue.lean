
import JSP000404Research.GenericForwardAngleLift
import JSP000404Research.ProjectionCanonicalRayBridge
import JSP000404Research.LocalDirectionCycle
import Mathlib.Tactic

/-!
# Generic local direction values are a projective-cut rotation

For the generic projection order, the global DirectionData value of an
incident unoriented edge is obtained from the same forward lifted angle used
in ProjectionCanonicalRayBridge.

Fix a centre i.  Let

  cut = projectionProjectiveCut p
      = projectionAngleBase(genericProjectionSlope p) + pi.

The canonical projective ray angle theta lies in [0,pi).  The generic forward
lift lies on the single branch (base,base+pi), so the local normalized
direction coordinate is exactly

  (theta-cut)/lambda,              if cut <= theta,
  (theta+pi-cut)/lambda,           if theta < cut.

Thus the local DirectionData cycle is literally the canonical projective ray
cycle cut at one common projective angle and rotated.  All remaining work in
identifying the two centre exponents is list/cyclic-gap bookkeeping.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open Real

theorem genericLocalDirectionValue_eq_forward
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (j : OtherVertex i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (genericDirectionData_sendov hp hcap ht hlam).localDirectionValue i j
      =
    (centreForwardLiftedAngle hp i j -
      projectionAngleBase (genericProjectionSlope p)) / lam := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  unfold DirectionData.localDirectionValue
  unfold centreForwardLiftedAngle
  by_cases hji : j.1 < i
  · simp only [hji, if_pos]
    rw [genericDirectionData_sendov_value]
  · have hij : i < j.1 := by
      have hle : i ≤ j.1 := le_of_not_gt hji
      exact lt_of_le_of_ne hle j.2.symm
    simp only [hji, if_false]
    rw [genericDirectionData_sendov_value]

/-- Below the projective cut, the canonical angle is the forward lifted angle,
so the local normalized coordinate is the lower cut-rotated branch. -/
theorem genericLocalDirectionValue_eq_below_cut
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (j : OtherVertex i)
    (hbelow :
      rayThetaAt (reindexedPoint_injective hp) i j <
        projectionProjectiveCut p) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (genericDirectionData_sendov hp hcap ht hlam).localDirectionValue i j
      =
    (rayThetaAt (reindexedPoint_injective hp) i j +
        Real.pi - projectionProjectiveCut p) / lam := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  rw [genericLocalDirectionValue_eq_forward
      hp hcap ht hlam i j]
  have hforward :=
    centreForwardLiftedAngle_eq_rayTheta_of_below_cut
      hp i j hbelow
  rw [hforward]
  unfold projectionProjectiveCut
  ring

/-- At or above the projective cut, the forward lifted angle is theta-pi, so
the local coordinate starts at zero at the cut. -/
theorem genericLocalDirectionValue_eq_above_cut
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (j : OtherVertex i)
    (habove :
      projectionProjectiveCut p ≤
        rayThetaAt (reindexedPoint_injective hp) i j) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (genericDirectionData_sendov hp hcap ht hlam).localDirectionValue i j
      =
    (rayThetaAt (reindexedPoint_injective hp) i j -
        projectionProjectiveCut p) / lam := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  rw [genericLocalDirectionValue_eq_forward
      hp hcap ht hlam i j]
  have hforward :=
    centreForwardLiftedAngle_eq_rayTheta_sub_pi_of_above_cut
      hp i j habove
  rw [hforward]
  unfold projectionProjectiveCut
  ring

/-- Unified piecewise projective-cut formula. -/
theorem genericLocalDirectionValue_eq_cutRotate
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (j : OtherVertex i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (genericDirectionData_sendov hp hcap ht hlam).localDirectionValue i j
      =
    if rayThetaAt (reindexedPoint_injective hp) i j <
        projectionProjectiveCut p then
      (rayThetaAt (reindexedPoint_injective hp) i j +
          Real.pi - projectionProjectiveCut p) / lam
    else
      (rayThetaAt (reindexedPoint_injective hp) i j -
          projectionProjectiveCut p) / lam := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  by_cases hbelow :
      rayThetaAt (reindexedPoint_injective hp) i j <
        projectionProjectiveCut p
  · rw [if_pos hbelow]
    exact genericLocalDirectionValue_eq_below_cut
      hp hcap ht hlam i j hbelow
  · rw [if_neg hbelow]
    exact genericLocalDirectionValue_eq_above_cut
      hp hcap ht hlam i j (le_of_not_gt hbelow)

/-- The scaling circumference is exactly pi/lambda=t. -/
theorem pi_div_lam_eq_t
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t) :
    Real.pi / lam = t := by
  rw [hlam]
  field_simp [Real.pi_ne_zero, ne_of_gt ht]

#print axioms genericLocalDirectionValue_eq_forward
#print axioms genericLocalDirectionValue_eq_below_cut
#print axioms genericLocalDirectionValue_eq_above_cut
#print axioms genericLocalDirectionValue_eq_cutRotate
#print axioms pi_div_lam_eq_t

end ProjectionOrdered
end JSP000404Research
