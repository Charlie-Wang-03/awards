import JSP000404Research.ProjectionCutLocalCycle
import JSP000404Research.CyclicQuotientRotation
import Mathlib.Tactic

/-!
# Exact quotient rotation for the projection-cut local cycle

The explicit local-direction cycle obtained from the generic projection cut
does not merely preserve the centre exponent.  Its entire cyclic quotient list
is the canonical centre quotient list rotated by the length of the low-angle
block.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open Real

section

variable {V : Type*} [Fintype V]
variable {p : V → Plane}
variable (hp : Function.Injective p)

local instance projectionOrder :
    LinearOrder (ProjectionOrdered V) :=
  projectionLinearOrder hp

theorem projectionCutLocalCycle_gapQuotients_eq_rotate
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    (projectionCutLocalCycle hp hcap ht hlam i C).gapQuotients
      =
    (quotientList t C.gaps).rotate
      (projectionCutLowAngles hp i C).length := by
  let low := projectionCutLowAngles hp i C
  let high := projectionCutHighAngles hp i C
  let unwrapped := high.map (fun theta => theta - Real.pi) ++ low
  have hangles :
      C.angles = low ++ high :=
    centreAngles_eq_cutLow_append_cutHigh hp i C
  have hne : low ++ high ≠ [] := by
    intro h
    apply C.angles_nonempty
    rw [hangles]
    exact h
  have hvalues :
      (projectionCutLocalCycle hp hcap ht hlam i C).values =
        unwrapped.map
          (affineAngleValue
            (projectionAngleBase (genericProjectionSlope p))
            lam) := by
    simpa [low,high,unwrapped] using
      projectionCutLocalCycle_values_eq_affine_unwrapped
        hp hcap ht hlam i C
  unfold LocalDirectionCycle.gapQuotients
  rw [hvalues]
  rw [linearCyclicGapQuotients_affine_eq_quotientList
      (projectionAngleBase (genericProjectionSlope p))
      lam t ht hlam unwrapped]
  have hgapRot :=
    normalizedProjectiveGaps_cut_rotate low high hne
  change
    quotientList t
      (normalizedProjectiveGaps
        (high.map (fun x => x - Real.pi) ++ low))
      =
    (quotientList t C.gaps).rotate low.length
  rw [hgapRot, quotientList_rotate]
  have hcentreGaps :
      normalizedProjectiveGaps (low ++ high) = C.gaps := by
    rw [← hangles]
    rfl
  rw [hcentreGaps]

theorem projectionCutLocalCycle_gapQuotients_perm_canonical
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    (projectionCutLocalCycle hp hcap ht hlam i C).gapQuotients
      ~ quotientList t C.gaps := by
  rw [projectionCutLocalCycle_gapQuotients_eq_rotate
    hp hcap ht hlam i C]
  exact List.rotate_perm _ _

#print axioms projectionCutLocalCycle_gapQuotients_eq_rotate
#print axioms projectionCutLocalCycle_gapQuotients_perm_canonical

end
end ProjectionOrdered
end JSP000404Research
