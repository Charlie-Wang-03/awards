import JSP000404Research.SecondLayerSupportOneSpectrum
import JSP000404Research.ThreeBandSpectrumRigidity
import JSP000404Research.ZeroUnitStepQuotient
import JSP000404Research.ProjectionRetainedPaletteBandBridge
import JSP000404Research.ProjectionLossZeroUnitStep
import Mathlib.Tactic

/-!
# Consecutive retained palette for support-one second-layer projected loss

A support-one deficit-two centre has canonical quotient spectrum {0,n-1}.
For a projected-loss second-layer centre the local projection-cut profile uses
exactly three non-top bands and saturates the one-layer band bound.  Saturation
transfers the quotient spectrum to cyclic band jumps, where the only extra
positive jumps are unit mismatches.  Therefore the three retained colour
labels are consecutive.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem planar_projectedLoss_supportOne_retainedPalette_consecutive
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
      i ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hsecond : centreExponent (C i) t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient (C i) t) = 1) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    ∃ m : ℕ,
      (retainedActive R i).map Fin.valEmbedding =
        {m,m+1,m+2} := by
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
    simpa [R,D,exponent,planarStandardResidualColoring,
      planarCentreExponent] using hloss

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap hn1 hdelta0 hdelta1 ht hlam C
  have hexpBound : ∀ q, exponent q ≤ n := by
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
      R exponent hexpBound hone hloss'

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

  obtain ⟨a,xs,hvalues⟩ :
      ∃ a xs, L.values = a :: xs := by
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
    exact
      (L.value_mem_bounds
        (by simpa [hvalues] using hx)).2
  have hall0 :
      ∀ x ∈ a :: xs, 0 ≤ x := by
    intro x hx
    exact
      (L.value_mem_bounds
        (by simpa [hvalues] using hx)).1

  let qs :=
    (cyclicRealGapsAt t (a :: xs)).map Nat.floor
  let bs :=
    cyclicBandJumps n
      ((a :: xs).map Nat.floor)

  have hle : List.Forall₂ (· ≤ ·) qs bs := by
    dsimp [qs,bs]
    exact cyclicFloorGaps_le_cyclicBandJumps
      a xs n ha0 hsorted hall hwidthR

  have hqEq :
      qs = L.gapQuotients := by
    dsimp [qs,L]
    unfold LocalDirectionCycle.gapQuotients
    rw [hvalues]
    rfl

  have hqExp :
      listExponent qs = n - 2 := by
    rw [hqEq]
    have hlocal :=
      projectionCutLocalCycle_exponent_eq_centreExponent
        hp hcap htpos hlam i (C i)
    simpa [L, LocalDirectionCycle.exponent, hsecond] using hlocal

  have hfloorSorted :
      ((a :: xs).map Nat.floor).Pairwise (· ≤ ·) :=
    floorLabels_pairwise a xs hsorted
  have hfloorBound :
      ∀ c ∈ (a :: xs).map Nat.floor, c ≤ n := by
    intro c hc
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc
    exact floorLabel_le_n_of_lt_n_succ
      (hall0 x hx) ((hall x hx).trans hwidthR)

  have hcardFloor :
      ((a :: xs).map Nat.floor).toFinset.card = 3 := by
    have hc := hoccCard
    rw [hvalues] at hc
    simpa [occupiedNatBands] using hc

  have hbExp :
      listExponent bs = n - 2 := by
    dsimp [bs]
    have h :=
      cyclicBandJumps_exponent_eq_total_sub_distinct
        n (Nat.floor a) (xs.map Nat.floor)
        (by simpa using hfloorSorted)
        (by
          intro c hc
          exact hfloorBound c (by simpa using hc))
    rw [hcardFloor] at h
    omega

  have hqSpec :
      ∀ q ∈ qs, q = 0 ∨ q = 1 ∨ q = n - 1 := by
    intro q hqmem
    have hqL : q ∈ L.gapQuotients := by
      rw [← hqEq]
      exact hqmem
    have hqCan :
        q ∈ quotientList t (C i).gaps :=
      mem_centreQuotients_of_mem_projectionCutLocalQuotients
        hp hcap htpos hlam i (C i) hqL
    have hspec :=
      deficitTwo_supportOne_quotient_spectrum
        (hp := reindexedPoint_injective hp)
        hn3 hdelta0 hdelta1 ht
        (C i) hsecond hsupport q hqCan
    rcases hspec with h0 | hN
    · exact Or.inl h0
    · exact Or.inr (Or.inr hN)

  have hbSpec :
      ∀ b ∈ bs, b = 0 ∨ b = 1 ∨ b = n - 1 :=
    bandJump_spectrum_of_quotient_spectrum
      (N := n - 1) (by omega)
      hle (by rw [hqExp,hbExp]) hqSpec

  have hbelowTop :
      ∀ c ∈ (Nat.floor a :: xs.map Nat.floor),
        c ≤ n - 1 := by
    intro c hc
    have hcMap :
        c ∈ (a :: xs).map Nat.floor := by
      simpa using hc
    have hcn := hfloorBound c hcMap
    have hcNotTop : c ≠ n := by
      intro hcnEq
      apply htopAbsent
      rw [hvalues]
      unfold occupiedNatBands
      rw [List.mem_toFinset]
      simpa [hcnEq] using hcMap
    omega

  obtain ⟨m,hm⟩ :=
    three_occupied_bands_consecutive_of_cyclic_spectrum
      (n := n) (a := Nat.floor a) (xs := xs.map Nat.floor)
      hn3
      (by simpa using hfloorSorted)
      (by simpa using hcardFloor)
      hbelowTop
      (by
        intro b hb
        exact hbSpec b (by
          dsimp [bs] at hb ⊢
          simpa using hb))

  have hoccConsecutive :
      occupiedNatBands L.values = {m,m+1,m+2} := by
    rw [hvalues]
    unfold occupiedNatBands
    simpa using hm

  have hbridge :=
    projectionCut_occupiedBands_eq_retainedActive_valMap
      hp hcap htpos hlam hwidth i (C i)
      (by simpa [R,D] using hresInactive)

  refine ⟨m,?_⟩
  have hbridge' :
      occupiedNatBands L.values =
        (retainedActive R i).map Fin.valEmbedding := by
    simpa [L,R,D] using hbridge
  rw [← hbridge']
  exact hoccConsecutive

#print axioms planar_projectedLoss_supportOne_retainedPalette_consecutive

end ProjectionOrdered
end JSP000404Research
