import JSP000404Research.InteriorPhaseSlipRayWitness
import JSP000404Research.ProjectionCutLocalCycle
import Mathlib.Tactic

/-!
# Actual planar angle witnesses from interior band phase slips

For the genuine planar generic-projection DirectionData, the local
normalised direction values are precisely the forward lifted ray angles
divided by lambda (up to a common additive base).

Therefore the ray pair extracted from a tight residual-inactive
local cycle gives three *distinct planar vertices* whose consecutive
lifted directions have a nonnegative physical angular difference
strictly smaller than lambda.

The difficult subsequent step is to globally match or compensate
these local short-angle witnesses across different centres.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open DirectionData
open OrderedEdgeColoring

theorem planar_tight_residual_inactive_has_short_angle_rays
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (htwidth : t < (n : ℝ) + 1)
    (i : ProjectionOrdered V)
    (C : ProjectionCentreCycle hp i)
    (htight :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let D := genericDirectionData_sendov hp hcap htpos hlam
      let L := projectionCutLocalCycle hp hcap htpos hlam i C
      L.exponent + (D.incidentBands (n + 1) i).card = n + 1)
    (hres :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let D := genericDirectionData_sendov hp hcap htpos hlam
      residualCoord n ∉
        active (standardResidualColoring D n
          (by exact_mod_cast htwidth)) i) :
    ∃ u v : OtherVertex i,
      u ≠ v ∧
        0 ≤ centreForwardLiftedAngle hp i v -
          centreForwardLiftedAngle hp i u ∧
        centreForwardLiftedAngle hp i v -
          centreForwardLiftedAngle hp i u < lam := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let L := projectionCutLocalCycle hp hcap htpos hlam i C
  change L.exponent + (D.incidentBands (n + 1) i).card =
    n + 1 at htight
  change residualCoord n ∉
    active (standardResidualColoring D n
      (by exact_mod_cast htwidth)) i at hres
  obtain ⟨u, v, pre, post, hsegment, hnonneg, hsmall, hband⟩ :=
    L.exists_adjacent_rays_with_short_band_crossing
      htwidth htight hres
  have hneq : u ≠ v := by
    intro heq
    subst v
    simp at hband
  have hlamPos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hu :=
    genericLocalDirectionValue_eq_forward
      hp hcap htpos hlam i u
  have hv :=
    genericLocalDirectionValue_eq_forward
      hp hcap htpos hlam i v
  have hnorm :
      (centreForwardLiftedAngle hp i v -
        centreForwardLiftedAngle hp i u) / lam =
      D.localDirectionValue i v - D.localDirectionValue i u := by
    calc
      (centreForwardLiftedAngle hp i v -
          centreForwardLiftedAngle hp i u) / lam =
        (centreForwardLiftedAngle hp i v -
          projectionAngleBase (genericProjectionSlope p)) / lam -
        (centreForwardLiftedAngle hp i u -
          projectionAngleBase (genericProjectionSlope p)) / lam := by
            ring
      _ = D.localDirectionValue i v -
            D.localDirectionValue i u := by
              rw [← hv, ← hu]
  have hphysical :
      centreForwardLiftedAngle hp i v -
        centreForwardLiftedAngle hp i u =
      (D.localDirectionValue i v -
        D.localDirectionValue i u) * lam := by
    calc
      centreForwardLiftedAngle hp i v -
          centreForwardLiftedAngle hp i u =
        ((centreForwardLiftedAngle hp i v -
          centreForwardLiftedAngle hp i u) / lam) * lam := by
            field_simp [ne_of_gt hlamPos]
      _ = (D.localDirectionValue i v -
            D.localDirectionValue i u) * lam := by rw [hnorm]
  have hangle0 :
      0 ≤ centreForwardLiftedAngle hp i v -
        centreForwardLiftedAngle hp i u := by
    rw [hphysical]
    exact mul_nonneg hnonneg hlamPos.le
  have hanglelt :
      centreForwardLiftedAngle hp i v -
        centreForwardLiftedAngle hp i u < lam := by
    have hh :
        (centreForwardLiftedAngle hp i v -
          centreForwardLiftedAngle hp i u) / lam < 1 := by
      rw [hnorm]
      exact hsmall
    have ht := (div_lt_iff₀ hlamPos).mp hh
    linarith
  exact ⟨u, v, hneq, hangle0, hanglelt⟩

#print axioms planar_tight_residual_inactive_has_short_angle_rays

end ProjectionOrdered
end JSP000404Research
