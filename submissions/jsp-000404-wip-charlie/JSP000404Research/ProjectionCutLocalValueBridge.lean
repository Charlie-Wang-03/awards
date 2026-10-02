import JSP000404Research.ProjectionLocalDirectionValue
import JSP000404Research.CutProjectiveBandPartition
import Mathlib.Tactic

/-!
# Generic local direction value equals the projection-cut normalized ray value

At the distinguished generic projective cut, the piecewise formulas defining
the generic DirectionData local coordinate and the cut-rotated canonical ray
coordinate are identical.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem genericLocalDirectionValue_eq_cutNormalizedRayTheta
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (j : OtherVertex i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (genericDirectionData_sendov hp hcap ht hlam).localDirectionValue i j
      =
    cutNormalizedRayTheta
      (reindexedPoint_injective hp) t
      (projectionProjectiveCut p) i j := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  rw [genericLocalDirectionValue_eq_cutRotate hp hcap ht hlam i j]
  unfold cutNormalizedRayTheta cutRayTheta
  by_cases hbelow :
      rayThetaAt (reindexedPoint_injective hp) i j <
        projectionProjectiveCut p
  · rw [if_pos hbelow, if_pos hbelow]
    rw [hlam]
    field_simp [Real.pi_ne_zero, ne_of_gt ht]
    ring
  · rw [if_neg hbelow, if_neg hbelow]
    rw [hlam]
    field_simp [Real.pi_ne_zero, ne_of_gt ht]
    ring

#print axioms genericLocalDirectionValue_eq_cutNormalizedRayTheta

end ProjectionOrdered
end JSP000404Research
