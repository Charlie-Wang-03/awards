import JSP000404Research.ThreeBandReverseSpectrumRigidity
import JSP000404Research.ProjectionRetainedPaletteBandBridge
import JSP000404Research.ZeroUnitStepQuotient
import JSP000404Research.SaturatedBandJumpMismatch
import Mathlib.Tactic

/-!
# Transition quotient dichotomy from a consecutive three-band palette

At a planar projected-loss second-layer support-two centre, suppose the three
retained active bands are consecutive.

The cut-local quotient list is pointwise dominated by the cyclic jumps of the
sorted band labels, while exact projected-loss saturation gives equality of
their list exponents.  The consecutive-three-band hypothesis forces every band
jump to lie in {0,1,n-1}.  Coordinatewise excess equality then forces every
genuine quotient to lie in the same spectrum.

A high-exponent transition certificate has a positive quotient qe belonging to
the genuine quotient list, hence qe is either 1 or n-1.
-/

namespace JSP000404Research

theorem quotient_spectrum_of_band_spectrum_exact_exponent
    {qs bs : List ℕ} {N : ℕ}
    (hN : 2 ≤ N)
    (hle : List.Forall₂ (· ≤ ·) qs bs)
    (hexp : listExponent qs = listExponent bs)
    (hbspec : ∀ b ∈ bs, b = 0 ∨ b = 1 ∨ b = N) :
    ∀ q ∈ qs, q = 0 ∨ q = 1 ∨ q = N := by
  have hexcess :=
    forall₂_excess_eq_of_forall₂_le_of_listExponent_eq
      hle hexp
  induction hle with
  | nil =>
      simp
  | @cons q b qs bs hqb htail ih =>
      have hheadExp :
          excess q = excess b :=
        (List.forall₂_cons.mp hexcess).1
      have htailExp :
          listExponent qs = listExponent bs := by
        simp only [listExponent, List.map_cons, List.sum_cons] at hexp
        have htailLe := listExponent_le_of_forall₂_le htail
        have hheadLe := excess_mono_nat hqb
        omega
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · have hbSpec := hbspec b (by simp)
        rcases hbSpec with rfl | rfl | hbN
        · left
          omega
        · have hq : q = 0 ∨ q = 1 := by omega
          rcases hq with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
        · subst b
          by_cases hq0 : q = 0
          · exact Or.inl hq0
          · have hqpos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
            unfold excess at hheadExp
            have hqN : q = N := by omega
            exact Or.inr (Or.inr hqN)
      · exact ih htailExp
          (fun b hb => hbspec b (by simp [hb]))
          x hx

namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_projectedLoss_supportTwo_consecutivePalette_transition_qe_dichotomy
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    (i : ProjectionOrdered V)
    (hloss :
      i ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hsecond :
      centreExponent (Cfam i) t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient (Cfam i) t) = 2)
    (hpalette :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R i).map Fin.valEmbedding =
        threeNatInterval m)
    (H :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t i (Cfam i)) :
    H.qe = 1 ∨ H.qe = n - 1 := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  have htpos :
      0 < t :=
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
  let exponent := planarCentreExponent hp Cfam
  let L :=
    projectionCutLocalCycle hp hcap htpos hlam i (Cfam i)

  have hloss' : i ∈ projectedLossVertices R exponent := by
    simpa [R,D,exponent,planarStandardResidualColoring,
      planarCentreExponent] using hloss

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap hn1 hdelta0 hdelta1 ht hlam Cfam
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

  have hoccBridge :=
    projectionCut_occupiedBands_eq_retainedActive_valMap
      hp hcap htpos hlam hwidth i (Cfam i)
      (by simpa [R,D] using hresInactive)
  have hocc :
      occupiedNatBands L.values = threeNatInterval m := by
    rw [hoccBridge]
    simpa [R,D,threeNatInterval] using hpalette

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
  have ha0 : 0 ≤ a := (L.value_mem_bounds haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using L.values_pairwise
  have hall0 :
      ∀ x ∈ a :: xs, 0 ≤ x := by
    intro x hx
    exact (L.value_mem_bounds (by simpa [hvalues] using hx)).1
  have hall :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact (L.value_mem_bounds (by simpa [hvalues] using hx)).2

  let qs :=
    (cyclicRealGapsAt t (a :: xs)).map Nat.floor
  let bs :=
    cyclicBandJumps n ((a :: xs).map Nat.floor)

  have hle : List.Forall₂ (· ≤ ·) qs bs := by
    dsimp [qs,bs]
    exact cyclicFloorGaps_le_cyclicBandJumps
      a xs n ha0 hsorted hall hwidthR

  have hqEq : qs = L.gapQuotients := by
    dsimp [qs,L]
    unfold LocalDirectionCycle.gapQuotients
    rw [hvalues]
    rfl

  have hqExp :
      listExponent qs = n - 2 := by
    rw [hqEq]
    have hlocal :=
      projectionCutLocalCycle_exponent_eq_centreExponent
        hp hcap htpos hlam i (Cfam i)
    simpa [L,LocalDirectionCycle.exponent,hsecond] using hlocal

  have hfloorSorted :
      ((a :: xs).map Nat.floor).Pairwise (· ≤ ·) :=
    floorLabels_pairwise a xs hsorted

  have hfloorBound :
      ∀ c ∈ (a :: xs).map Nat.floor, c ≤ n := by
    intro c hc
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc
    exact floorLabel_le_n_of_lt_n_succ
      (hall0 x hx)
      ((hall x hx).trans hwidthR)

  have hset :
      ((a :: xs).map Nat.floor).toFinset =
        threeNatInterval m := by
    have hocc' : occupiedNatBands (a :: xs) =
        threeNatInterval m := by
      simpa [L,hvalues] using hocc
    simpa [occupiedNatBands] using hocc'

  have hbelowTop : m + 2 ≤ n - 1 := by
    have hm2 :
        m+2 ∈ ((a :: xs).map Nat.floor).toFinset := by
      rw [hset]
      simp [threeNatInterval]
    have hm2List :
        m+2 ∈ (a :: xs).map Nat.floor := by
      simpa using hm2
    have hleN := hfloorBound (m+2) hm2List
    have hnotTop : m+2 ≠ n := by
      intro heq
      have hnOcc : n ∈ occupiedNatBands L.values := by
        rw [hvalues]
        change n ∈ ((a :: xs).map Nat.floor).toFinset
        simpa [heq] using hm2
      have hbridge :=
        L.occupiedNatBands_values_eq_incident_val_map
          (n + 1) (by exact_mod_cast le_of_lt hwidthR)
      rw [hbridge] at hnOcc
      obtain ⟨c,hc,hval⟩ := Finset.mem_map.mp hnOcc
      have hcRes : c = residualCoord n := by
        apply Fin.ext
        simpa [residualCoord] using hval
      have hcActive : residualCoord n ∈ active R i := by
        have hactiveEq :
            active R i = D.incidentBands (n+1) i := by
          simpa [R] using
            standardResidual_active_eq_incidentBands_succ
              D n hwidth i
        rw [hactiveEq]
        simpa [hcRes] using hc
      exact hresInactive hcActive
    omega

  have hbSpec :
      ∀ b ∈ bs, b = 0 ∨ b = 1 ∨ b = n - 1 := by
    dsimp [bs]
    exact cyclicBandJumps_three_consecutive_spectrum
      hn3
      (by simpa using hfloorSorted)
      (by simpa [threeNatInterval] using hset)
      hbelowTop

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
    have hcard :
        ((a :: xs).map Nat.floor).toFinset.card = 3 := by
      rw [hset]
      simp [threeNatInterval]
    rw [hcard] at h
    omega

  have hqSpecLocal :
      ∀ q ∈ qs, q = 0 ∨ q = 1 ∨ q = n - 1 :=
    quotient_spectrum_of_band_spectrum_exact_exponent
      (by omega : 2 ≤ n-1)
      hle (by rw [hqExp,hbExp]) hbSpec

  have hHLocal :
      H.qe ∈ qs := by
    have hrot :=
      projectionCutLocalCycle_gapQuotients_eq_rotate
        hp hcap htpos hlam i (Cfam i)
    have hmemCan : H.qe ∈ quotientList t (Cfam i).gaps :=
      H.qe_mem
    have hmemLocal :
        H.qe ∈ L.gapQuotients := by
      rw [hrot]
      simpa using hmemCan
    rw [← hqEq] at hmemLocal
    exact hmemLocal

  have hspec := hqSpecLocal H.qe hHLocal
  rcases hspec with h0 | h1 | hN
  · exact False.elim (H.qe_ne h0)
  · exact Or.inl h1
  · exact Or.inr hN

#print axioms quotient_spectrum_of_band_spectrum_exact_exponent
#print axioms planar_projectedLoss_supportTwo_consecutivePalette_transition_qe_dichotomy

end ProjectionOrdered
end JSP000404Research
