import JSP000404Research.ThreeWholeCubePartnerExtremeProfileContradiction
import JSP000404Research.ThreeWholeCubeSourceExtremeProfileContradiction
import JSP000404Research.PlanarCentreExponent
import Mathlib.Tactic

/-!
# Final all-support-two whole-cube contradiction under the one-layer bound

This module closes the finite all-four-support-two whole-cube core without
using the ordered-adjacent / staircase route.

For the standard planar residual colouring, assume the already established
one-layer active-colour bound

  card(active(q)) <= n - exponent(q) + 1.

The retained-code star then forces one of the four vertices to be a global
order extreme.

* source global minimum / maximum -> source profile 000 / 111;
* owner-partner global minimum / maximum -> source profile 100 / 011,
  with the latter relabelled as 110.

The four profile contradiction cores eliminate all eight extreme branches.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_threeWholeCube_allSupportTwo_impossible_of_oneLayer
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {v s₁ s₂ s₃ : ProjectionOrdered V}
    (hvs1 : v ≠ s₁) (hvs2 : v ≠ s₂) (hvs3 : v ≠ s₃)
    {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂) (hc13 : c₁ ≠ c₃) (hc23 : c₂ ≠ c₃)
    (hactive :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R v = {c₁,c₂,c₃})
    (hvLoss :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      let exponent := planarCentreExponent (t := t) hp Cfam
      v ∈ projectedLossVertices R exponent)
    (hs1Loss :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      let exponent := planarCentreExponent (t := t) hp Cfam
      s₁ ∈ projectedLossVertices R exponent)
    (hs2Loss :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      let exponent := planarCentreExponent (t := t) hp Cfam
      s₂ ∈ projectedLossVertices R exponent)
    (hs3Loss :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      let exponent := planarCentreExponent (t := t) hp Cfam
      s₃ ∈ projectedLossVertices R exponent)
    (hvSecond : centreExponent (Cfam v) t = n - 2)
    (hs1Second : centreExponent (Cfam s₁) t = n - 2)
    (hs2Second : centreExponent (Cfam s₂) t = n - 2)
    (hs3Second : centreExponent (Cfam s₃) t = n - 2)
    (hvSupport : positiveSupport (centreQuotient (Cfam v) t) = 2)
    (hs1Support : positiveSupport (centreQuotient (Cfam s₁) t) = 2)
    (hs2Support : positiveSupport (centreQuotient (Cfam s₂) t) = 2)
    (hs3Support : positiveSupport (centreQuotient (Cfam s₃) t) = 2)
    (h₁ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₁ v c₁)
    (h₂ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₂ v c₂)
    (h₃ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₃ v c₃)
    (hone :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      let exponent := planarCentreExponent (t := t) hp Cfam
      ∀ q, (active R q).card ≤ n - exponent q + 1) :
    False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn3 : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith

  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent (t := t) hp Cfam

  have hactive' : retainedActive R v = {c₁,c₂,c₃} := by
    simpa [R] using hactive
  have hvLoss' : v ∈ projectedLossVertices R exponent := by
    simpa [R,exponent] using hvLoss
  have hs1Loss' : s₁ ∈ projectedLossVertices R exponent := by
    simpa [R,exponent] using hs1Loss
  have hs2Loss' : s₂ ∈ projectedLossVertices R exponent := by
    simpa [R,exponent] using hs2Loss
  have hs3Loss' : s₃ ∈ projectedLossVertices R exponent := by
    simpa [R,exponent] using hs3Loss
  have h1' : WholeCubeQTPair R s₁ v c₁ := by simpa [R] using h₁
  have h2' : WholeCubeQTPair R s₂ v c₂ := by simpa [R] using h₂
  have h3' : WholeCubeQTPair R s₃ v c₃ := by simpa [R] using h₃
  have hone' : ∀ q, (active R q).card ≤ n - exponent q + 1 := by
    simpa [R,exponent] using hone
  have hexp : ∀ q, exponent q ≤ n :=
    planarCentreExponent_le_n_light
      hp hn1 hdelta0 hdelta1 ht Cfam

  have hc1V : c₁ ∈ retainedActive R v := by rw [hactive']; simp
  have hc2V : c₂ ∈ retainedActive R v := by rw [hactive']; simp
  have hc3V : c₃ ∈ retainedActive R v := by rw [hactive']; simp

  have hextreme :=
    threeWholeCubePartners_has_global_extreme
      R exponent hexp hone'
      hc12 hc13 hc23
      hactive'
      hvLoss' hs1Loss' hs2Loss' hs3Loss'
      h1' h2' h3'

  rcases hextreme with
      (hvMin | hvMax)
    | (hs1Min | hs1Max)
    | (hs2Min | hs2Max)
    | (hs3Min | hs3Max)

  · have hfalse : AllRetainedBitsFalse R v :=
      global_min_allRetainedBitsFalse R hvMin
    exact source_000_profile_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc12 hc13 hc23
      hactive h₁ h₂ h₃
      hs1Second hs2Second hs3Second
      hs1Support hs2Support hs3Support
      (by simpa [R] using hfalse c₁ hc1V)
      (by simpa [R] using hfalse c₂ hc2V)
      (by simpa [R] using hfalse c₃ hc3V)

  · have htrue : AllRetainedBitsTrue R v :=
      global_max_allRetainedBitsTrue R hvMax
    exact source_111_profile_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc12 hc13 hc23
      hactive h₁ h₂ h₃
      hs1Second hs2Second hs3Second
      hs1Support hs2Support hs3Support
      (by simpa [R] using htrue c₁ hc1V)
      (by simpa [R] using htrue c₂ hc2V)
      (by simpa [R] using htrue c₃ hc3V)

  · exact owner_partner_globalMin_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc12 hc13 hc23
      hactive h₁ h₂ h₃
      hvSecond hs2Second hs3Second
      hvSupport hs2Support hs3Support
      hs1Min

  · exact owner_partner_globalMax_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc12 hc13 hc23
      hactive h₁ h₂ h₃
      hvSecond hs2Second hs3Second
      hvSupport hs2Support hs3Support
      hs1Max

  · have hactive₂ :
      retainedActive R v = {c₂,c₁,c₃} := by
      simpa [Finset.insert_comm, Finset.insert_left_comm, Finset.insert_assoc]
        using hactive'
    exact owner_partner_globalMin_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc12.symm hc23 hc13
      (by simpa [R] using hactive₂)
      h₂ h₁ h₃
      hvSecond hs1Second hs3Second
      hvSupport hs1Support hs3Support
      hs2Min

  · have hactive₂ :
      retainedActive R v = {c₂,c₁,c₃} := by
      simpa [Finset.insert_comm, Finset.insert_left_comm, Finset.insert_assoc]
        using hactive'
    exact owner_partner_globalMax_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc12.symm hc23 hc13
      (by simpa [R] using hactive₂)
      h₂ h₁ h₃
      hvSecond hs1Second hs3Second
      hvSupport hs1Support hs3Support
      hs2Max

  · have hactive₃ :
      retainedActive R v = {c₃,c₁,c₂} := by
      simpa [Finset.insert_comm, Finset.insert_left_comm, Finset.insert_assoc]
        using hactive'
    exact owner_partner_globalMin_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc13.symm hc23.symm hc12
      (by simpa [R] using hactive₃)
      h₃ h₁ h₂
      hvSecond hs1Second hs2Second
      hvSupport hs1Support hs2Support
      hs3Min

  · have hactive₃ :
      retainedActive R v = {c₃,c₁,c₂} := by
      simpa [Finset.insert_comm, Finset.insert_left_comm, Finset.insert_assoc]
        using hactive'
    exact owner_partner_globalMax_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc13.symm hc23.symm hc12
      (by simpa [R] using hactive₃)
      h₃ h₁ h₂
      hvSecond hs1Second hs2Second
      hvSupport hs1Support hs2Support
      hs3Max

#print axioms planar_threeWholeCube_allSupportTwo_impossible_of_oneLayer

end ProjectionOrdered
end JSP000404Research
