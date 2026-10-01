import JSP000404Research.SecondLayerUnitTransitionBandRigidity
import JSP000404Research.ProjectionLossZeroUnitStep
import Mathlib.Tactic

/-!
# Projected-loss unit-transition support-two consecutive palette

A planar projected-loss second-layer centre has exactly three retained active
coordinates and does not use the residual top coordinate n.  Through the
projection-cut local-cycle bridge these become exactly three occupied local
bands below n.

If the centre is support-two and carries a transition certificate with qe=1,
the unit-transition band-rigidity theorem forces those three occupied bands
to be consecutive.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem planar_projectedLoss_unitSupportTwo_threeBands_consecutive
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
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
        sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
      let D :=
        genericDirectionData_sendov hp hcap htpos hlam
      let hwidth : t < (n + 1 : ℕ) := by
        rw [ht]
        exact_mod_cast
          (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
      let R :=
        standardResidualColoring D n hwidth
      let exponent : ProjectionOrdered V → ℕ :=
        fun q => centreExponent (C q) t
      i ∈ projectedLossVertices R exponent)
    (hsecond : centreExponent (C i) t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient (C i) t) = 2)
    (cert :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t i (C i))
    (hqe : cert.qe = 1) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let htpos : 0 < t :=
      sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
    let L :=
      projectionCutLocalCycle hp hcap htpos hlam i (C i)
    ∃ m : ℕ,
      occupiedNatBands L.values = {m, m + 1, m + 2} := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  have htpos : 0 < t :=
    sendov_scale_pos hn1 hdelta0 ht
  have hwidthR : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hwidth : t < (n + 1 : ℕ) := by
    exact_mod_cast hwidthR

  let D :=
    genericDirectionData_sendov hp hcap htpos hlam
  let R : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n hwidth
  let exponent : ProjectionOrdered V → ℕ :=
    fun q => centreExponent (C q) t
  let L :=
    projectionCutLocalCycle hp hcap htpos hlam i (C i)

  have hloss' : i ∈ projectedLossVertices R exponent := by
    simpa [R,D,exponent] using hloss

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap hn1 hdelta0 hdelta1 ht hlam C
  have hexp : ∀ q, exponent q ≤ n := by
    intro q
    exact Nat.le_of_lt
      (by simpa [exponent] using hprofile.1 q)
  have hone :
      ∀ q, (active R q).card ≤ n - exponent q + 1 := by
    intro q
    simpa [R,D,exponent] using hprofile.2 q

  have hresInactive :
      residualCoord n ∉ active R i :=
    residual_inactive_of_mem_projectedLossVertices
      R exponent hexp hone hloss'

  have hsecond' : exponent i = n - 2 := by
    simpa [exponent] using hsecond

  have hretCard :
      (retainedActive R i).card = 3 :=
    secondLayerLoss_retainedActive_card_eq_three
      R exponent hloss' hsecond'

  have hactiveCard :
      (active R i).card = 3 := by
    rw [active_card_eq_retainedActive_card_of_residual_not_mem
      R i hresInactive]
    exact hretCard

  have hactiveEq :
      active R i = D.incidentBands (n + 1) i := by
    simpa [R] using
      standardResidual_active_eq_incidentBands_succ
        D n hwidth i

  have hoccCard :
      (occupiedNatBands L.values).card = 3 := by
    have hocc :=
      L.occupiedNatBands_values_card_eq_incidentBands_card
        (n + 1) (by exact_mod_cast le_of_lt hwidthR)
    rw [← hactiveEq] at hocc
    rw [hactiveCard] at hocc
    exact hocc

  have htopAbsent :
      n ∉ occupiedNatBands L.values := by
    intro hnOcc
    have hbands :=
      L.occupiedNatBands_values_eq_incident_val_map
        (n + 1) (by exact_mod_cast le_of_lt hwidthR)
    rw [hbands] at hnOcc
    obtain ⟨c,hc,hval⟩ := Finset.mem_map.mp hnOcc
    have hcRes : c = residualCoord n := by
      apply Fin.ext
      simpa [residualCoord] using hval
    have hresIncident :
        residualCoord n ∈ D.incidentBands (n + 1) i := by
      simpa [hcRes] using hc
    have hresActive : residualCoord n ∈ active R i := by
      rw [hactiveEq]
      exact hresIncident
    exact hresInactive hresActive

  exact projectionCut_unitSupportTwo_threeBands_consecutive
    hp hcap hn3 hdelta0 hdeltaHalf ht hlam
    i (C i) hsecond hsupport cert hqe
    (by simpa [L] using hoccCard)
    (by simpa [L] using htopAbsent)

#print axioms planar_projectedLoss_unitSupportTwo_threeBands_consecutive

end ProjectionOrdered
end JSP000404Research
