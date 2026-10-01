import JSP000404Research.ProjectionCutLocalCycle
import JSP000404Research.StandardResidual
import Mathlib.Tactic

/-!
# Projection-cut occupied bands equal retained residual palette

For the standard residual colouring, full active colours are the first n+1
incident bands while retained active colours are the first n incident bands.

The projection-cut local cycle sees exactly the natural labels of the full
incident-band set.  If the residual top colour n is inactive, then no incident
band has label n, so the full occupied natural-label set is exactly the val-map
of the retained active palette.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem projectionCut_occupiedBands_eq_retainedActive_valMap
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (hwidth : t < (n + 1 : ℕ))
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hresInactive :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let D :=
        genericDirectionData_sendov hp hcap htpos hlam
      let R :=
        standardResidualColoring D n hwidth
      residualCoord n ∉ active R i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let D :=
      genericDirectionData_sendov hp hcap htpos hlam
    let R :=
      standardResidualColoring D n hwidth
    let L :=
      projectionCutLocalCycle hp hcap htpos hlam i C
    occupiedNatBands L.values =
      (retainedActive R i).map Fin.valEmbedding := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let D :=
    genericDirectionData_sendov hp hcap htpos hlam
  let R : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n hwidth
  let L :=
    projectionCutLocalCycle hp hcap htpos hlam i C

  have hresInactive' : residualCoord n ∉ active R i := by
    simpa [D,R] using hresInactive

  have hocc :
      occupiedNatBands L.values =
        (D.incidentBands (n + 1) i).map Fin.valEmbedding := by
    exact L.occupiedNatBands_values_eq_incident_val_map
      (n + 1) (by exact_mod_cast le_of_lt hwidth)

  have hret :
      retainedActive R i = D.incidentBands n i := by
    simpa [R] using
      standardResidual_retainedActive_eq_incidentBands
        D n hwidth i

  have hact :
      active R i = D.incidentBands (n + 1) i := by
    simpa [R] using
      standardResidual_active_eq_incidentBands_succ
        D n hwidth i

  rw [hocc,hret]
  ext m
  constructor
  · intro hm
    obtain ⟨c,hc,hcm⟩ := Finset.mem_map.mp hm
    have hcActive : c ∈ active R i := by
      rw [hact]
      exact hc
    have hcNotRes : c ≠ residualCoord n := by
      intro heq
      subst c
      exact hresInactive' hcActive
    have hcValLt : c.val < n := by
      have hcLe : c.val ≤ n := by
        omega
      by_contra hnot
      have hcValEq : c.val = n := by omega
      apply hcNotRes
      apply Fin.ext
      simpa [residualCoord] using hcValEq
    let d : Fin n := ⟨c.val,hcValLt⟩
    have hcFloor :=
      (DirectionData.mem_incidentBands_iff_exists_local_floor
        D (n + 1) i c).1 hc
    obtain ⟨j,hj⟩ := hcFloor
    have hd :
        d ∈ D.incidentBands n i := by
      apply
        (DirectionData.mem_incidentBands_iff_exists_local_floor
          D n i d).2
      refine ⟨j,?_⟩
      simpa [d] using hj
    apply Finset.mem_map.mpr
    refine ⟨d,hd,?_⟩
    have hval : c.val = m := by
      simpa using hcm
    simpa [d] using hval
  · intro hm
    obtain ⟨d,hd,hdm⟩ := Finset.mem_map.mp hm
    let c : Fin (n + 1) := d.castSucc
    have hdFloor :=
      (DirectionData.mem_incidentBands_iff_exists_local_floor
        D n i d).1 hd
    obtain ⟨j,hj⟩ := hdFloor
    have hc :
        c ∈ D.incidentBands (n + 1) i := by
      apply
        (DirectionData.mem_incidentBands_iff_exists_local_floor
          D (n + 1) i c).2
      refine ⟨j,?_⟩
      simpa [c] using hj
    apply Finset.mem_map.mpr
    refine ⟨c,hc,?_⟩
    have hval : d.val = m := by
      simpa using hdm
    simpa [c] using hval

#print axioms projectionCut_occupiedBands_eq_retainedActive_valMap

end ProjectionOrdered
end JSP000404Research
