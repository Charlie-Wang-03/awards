import JSP000404Research.ProjectionStandardBandBudget
import JSP000404Research.ResidualLossWords
import JSP000404Research.LinearSaturatedEndpointDichotomy
import JSP000404Research.ProjectionCutLocalCycle
import Mathlib.Tactic

/-!
# Lower-branch projected-loss vertices force a zero-unit local crossing

An exact projected loss vertex satisfies

  exponent = projectedFree + 1,

hence the residual colour is inactive and the retained palette has the exact
one-layer-saturated cardinality.  Residual inactivity means the full active
palette has the same cardinality as the retained palette.  Therefore the
local full-band inequality is saturated.

In the lower branch delta < 1/2, LinearSaturatedEndpointDichotomy says that a
saturated local cycle either occupies both boundary bands 0 and n, or contains
a zero-quotient unit-band crossing.  The first alternative would activate the
residual top band n, contradicting projected-loss rigidity.

Thus every planar projected-loss vertex carries a concrete zero-unit crossing.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem active_card_eq_retainedActive_card_of_residual_not_mem
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V)
    (hres : residualCoord n ∉ active C v) :
    (active C v).card = (retainedActive C v).card := by
  classical
  let R : Finset (Fin (n + 1)) :=
    (retainedActive C v).map Fin.castSuccEmb
  have hRsub : R ⊆ active C v := by
    intro c hc
    rcases Finset.mem_map.mp hc with ⟨d, hd, rfl⟩
    exact (castSucc_mem_active_iff_mem_retainedActive C v d).2 hd
  have hsub : active C v ⊆ R := by
    intro c hc
    by_cases hlt : c.val < n
    · let d : Fin n := ⟨c.val, hlt⟩
      have hdcast : d.castSucc = c := by
        apply Fin.ext
        rfl
      have hdActive :
          d ∈ retainedActive C v := by
        apply (castSucc_mem_active_iff_mem_retainedActive C v d).1
        simpa [hdcast] using hc
      exact Finset.mem_map.mpr ⟨d, hdActive, hdcast⟩
    · have hcval : c.val = n := by
        have hcLt := c.isLt
        omega
      have hcres : c = residualCoord n := by
        apply Fin.ext
        simpa [residualCoord] using hcval
      exact False.elim (hres (by simpa [hcres] using hc))
  have heq : active C v = R :=
    Finset.Subset.antisymm hsub hRsub
  rw [heq]
  simp [R]

#print axioms active_card_eq_retainedActive_card_of_residual_not_mem

end OrderedEdgeColoring

namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_projectedLoss_forces_zeroUnitStep
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (i : ProjectionOrdered V)
    (hloss :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let htpos : 0 < t :=
        sendov_scale_pos hn hdelta0 ht
      let D :=
        genericDirectionData_sendov hp hcap htpos hlam
      let hwidth : t < (n + 1 : ℕ) := by
        rw [ht]
        exact_mod_cast
          (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
      let B :=
        standardResidualColoring D n hwidth
      let exponent : ProjectionOrdered V → ℕ :=
        fun j => centreExponent (C j) t
      i ∈ projectedLossVertices B exponent) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let htpos : 0 < t :=
      sendov_scale_pos hn hdelta0 ht
    let D :=
      genericDirectionData_sendov hp hcap htpos hlam
    let L :=
      projectionCutLocalCycle hp hcap htpos hlam i (C i)
    ∃ a xs,
      L.values = a :: xs ∧
      HasZeroQuotientUnitStep a xs := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hdelta1 : delta < 1 := by linarith
  have htpos : 0 < t :=
    sendov_scale_pos hn hdelta0 ht
  have hwidthR : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hwidth : t < (n + 1 : ℕ) := by
    exact_mod_cast hwidthR

  let D :=
    genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n hwidth
  let exponent : ProjectionOrdered V → ℕ :=
    fun j => centreExponent (C j) t
  let L :=
    projectionCutLocalCycle hp hcap htpos hlam i (C i)

  have hloss' : i ∈ projectedLossVertices B exponent := by
    simpa [B, D, exponent] using hloss

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap hn hdelta0 hdelta1 ht hlam C
  have hexp : ∀ j, exponent j ≤ n := by
    intro j
    exact Nat.le_of_lt (by simpa [exponent] using hprofile.1 j)
  have hone :
      ∀ j, (active B j).card ≤ n - exponent j + 1 := by
    intro j
    simpa [B, D, exponent] using hprofile.2 j

  have hresInactive :
      residualCoord n ∉ active B i :=
    residual_inactive_of_mem_projectedLossVertices
      B exponent hexp hone hloss'

  have hlossEq :
      exponent i = projectedFree B i + 1 :=
    (mem_projectedLossVertices B exponent i).1 hloss'

  have hrigid :=
    exact_projected_loss_rigidity
      B exponent hexp hone hlossEq rfl
  have hactiveCard :
      (active B i).card = n - exponent i + 1 := by
    rw [active_card_eq_retainedActive_card_of_residual_not_mem
      B i hresInactive]
    exact hrigid.2

  have hactiveEq :
      active B i = D.incidentBands (n + 1) i := by
    simpa [B] using
      standardResidual_active_eq_incidentBands_succ D n hwidth i

  have hlocalExp :
      L.exponent = exponent i := by
    dsimp [L, exponent]
    exact projectionCutLocalCycle_exponent_eq_centreExponent
      hp hcap htpos hlam i (C i)

  have hoccCard :
      (occupiedNatBands L.values).card =
        (D.incidentBands (n + 1) i).card := by
    exact L.occupiedNatBands_values_card_eq_incidentBands_card
      (n + 1) (by exact_mod_cast le_of_lt hwidthR)

  have hsat :
      L.exponent + (occupiedNatBands L.values).card = n + 1 := by
    rw [hlocalExp, hoccCard, ← hactiveEq, hactiveCard]
    have hk := hexp i
    omega

  obtain ⟨a,xs,hvalues⟩ : ∃ a xs, L.values = a :: xs := by
    cases hv : L.values with
    | nil =>
        exact False.elim (L.values_nonempty hv)
    | cons a xs =>
        exact ⟨a,xs,hv⟩

  have haMem : a ∈ L.values := by
    rw [hvalues]
    simp
  have ha0 : 0 ≤ a :=
    (L.value_mem_bounds haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using L.values_pairwise
  have hall :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact (L.value_mem_bounds
      (by simpa [hvalues] using hx)).2
  have hsat' :
      listExponent
          (linearCyclicGapQuotients t (a :: xs)) +
        (occupiedNatBands (a :: xs)).card
        = n + 1 := by
    simpa [L, LocalDirectionCycle.exponent,
      LocalDirectionCycle.gapQuotients, hvalues] using hsat

  rcases saturated_boundaryBands_or_zeroUnitStep
      a xs ha0 hsorted hall ht hdeltaHalf hsat'
    with hboundary | hstep
  · exfalso
    have hnOcc : n ∈ occupiedNatBands (a :: xs) := by
      rw [occupiedNatBands, List.mem_toFinset, List.mem_map]
      exact ⟨xs.getLastD a,
        List.getLastD_mem_cons a xs,
        hboundary.2⟩
    have hnOccL : n ∈ occupiedNatBands L.values := by
      simpa [hvalues] using hnOcc
    have hbands :=
      L.occupiedNatBands_values_eq_incident_val_map
        (n + 1) (by exact_mod_cast le_of_lt hwidthR)
    rw [hbands] at hnOccL
    obtain ⟨c,hc,hval⟩ := Finset.mem_map.mp hnOccL
    have hcRes : c = residualCoord n := by
      apply Fin.ext
      simpa [residualCoord] using hval
    have hresIncident :
        residualCoord n ∈ D.incidentBands (n + 1) i := by
      simpa [hcRes] using hc
    have hresActive : residualCoord n ∈ active B i := by
      rw [hactiveEq]
      exact hresIncident
    exact hresInactive hresActive
  · exact ⟨a,xs,hvalues,hstep⟩

#print axioms planar_projectedLoss_forces_zeroUnitStep

end ProjectionOrdered
end JSP000404Research
