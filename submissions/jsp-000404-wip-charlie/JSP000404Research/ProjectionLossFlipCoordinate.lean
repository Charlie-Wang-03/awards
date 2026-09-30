import JSP000404Research.ProjectionLossZeroUnitStep
import Mathlib.Tactic

/-!
# A concrete retained flip coordinate at every planar loss vertex

The zero-unit-step witness at a projected-loss vertex is still stated only in
terms of the sorted local real values. This file extracts an actual retained
band coordinate c < n.

If x,y are the zero-quotient unit crossing, then

  floor y = floor x + 1.

Because a projected-loss vertex is residual-inactive, the top band n is not
incident. Hence floor y < n, so floor x < n as well. The coordinate
c = floor x is therefore retained and active at the loss vertex.

Consequently flipping c sends every retained completion word of the loss
vertex outside its own completion cube.
-/

namespace JSP000404Research

theorem exists_values_of_hasZeroQuotientUnitStep
    {a : ℝ} {xs : List ℝ}
    (h : HasZeroQuotientUnitStep a xs) :
    ∃ x y : ℝ,
      x ∈ a :: xs ∧
      y ∈ a :: xs ∧
      Nat.floor y = Nat.floor x + 1 ∧
      Nat.floor (y - x) = 0 := by
  induction xs generalizing a with
  | nil =>
      simp [HasZeroQuotientUnitStep] at h
  | cons b bs ih =>
      rw [hasZeroQuotientUnitStep_cons] at h
      rcases h with hhead | htail
      · exact ⟨a,b,by simp,by simp,hhead.1,hhead.2⟩
      · obtain ⟨x,y,hx,hy,hband,hgap⟩ :=
          ih (a := b) htail
        exact ⟨x,y,by simp at hx ⊢; exact Or.inr hx,
          by simp at hy ⊢; exact Or.inr hy,
          hband,hgap⟩

#print axioms exists_values_of_hasZeroQuotientUnitStep

namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_projectedLoss_has_retained_active_flip_coordinate
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
    let hwidth : t < (n + 1 : ℕ) := by
      rw [ht]
      exact_mod_cast
        (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
    let B :=
      standardResidualColoring D n hwidth
    ∃ c : Fin n,
      c ∈ retainedActive B i ∧
      ∀ word : Fin n → Bool,
        word ∈ retainedCompletionWords B i →
        flipBoolWordAt word c ∉ retainedCompletionWords B i := by
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
    simpa [B,D,exponent] using hloss

  obtain ⟨a,xs,hvalues,hstep⟩ :=
    planar_projectedLoss_forces_zeroUnitStep
      hp hcap hn hdelta0 hdeltaHalf ht hlam C i
      (by simpa [B,D,exponent] using hloss')

  obtain ⟨x,y,hx,hy,hband,hgap⟩ :=
    exists_values_of_hasZeroQuotientUnitStep hstep

  have hxL : x ∈ L.values := by
    simpa [L,hvalues] using hx
  have hyL : y ∈ L.values := by
    simpa [L,hvalues] using hy

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap hn hdelta0 hdelta1 ht hlam C
  have hexp : ∀ j, exponent j ≤ n := by
    intro j
    exact Nat.le_of_lt (by simpa [exponent] using hprofile.1 j)
  have hone :
      ∀ j, (active B j).card ≤ n - exponent j + 1 := by
    intro j
    simpa [B,D,exponent] using hprofile.2 j
  have hresInactive :
      residualCoord n ∉ active B i :=
    residual_inactive_of_mem_projectedLossVertices
      B exponent hexp hone hloss'

  have hy0 : 0 ≤ y :=
    (L.value_mem_bounds hyL).1
  have hyT : y < t :=
    (L.value_mem_bounds hyL).2
  have hyTop : Nat.floor y < n + 1 := by
    apply (Nat.floor_lt hy0).2
    exact hyT.trans hwidthR

  have hyBand : Nat.floor y < n := by
    by_contra hnot
    have hEq : Nat.floor y = n := by omega
    have hinc :
        residualCoord n ∈ D.incidentBands (n + 1) i := by
      apply (D.mem_incidentBands_iff_exists_local_floor
        (n + 1) i (residualCoord n)).2
      rw [LocalDirectionCycle.values, List.mem_map] at hyL
      obtain ⟨j,hj,rfl⟩ := hyL
      refine ⟨j, ?_⟩
      simpa [residualCoord] using hEq
    have hactiveEq :
        active B i = D.incidentBands (n + 1) i := by
      simpa [B] using
        standardResidual_active_eq_incidentBands_succ
          D n hwidth i
    exact hresInactive (by rw [hactiveEq]; exact hinc)

  have hxBand : Nat.floor x < n := by
    omega
  let c : Fin n := ⟨Nat.floor x, hxBand⟩

  have hcIncident : c ∈ D.incidentBands n i := by
    apply (D.mem_incidentBands_iff_exists_local_floor n i c).2
    rw [LocalDirectionCycle.values, List.mem_map] at hxL
    obtain ⟨j,hj,rfl⟩ := hxL
    refine ⟨j, ?_⟩
    rfl

  have hcRetained : c ∈ retainedActive B i := by
    have heq :=
      standardResidual_retainedActive_eq_incidentBands
        D n hwidth i
    rw [heq]
    exact hcIncident

  refine ⟨c,hcRetained,?_⟩
  intro word hword
  exact flip_active_not_mem_completion B hword hcRetained

#print axioms planar_projectedLoss_has_retained_active_flip_coordinate

end ProjectionOrdered
end JSP000404Research
