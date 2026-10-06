import JSP000404Research.ThreeWholeCubeSourceMixedProfileContradiction
import JSP000404Research.ThreeWholeCubeSourceExtremeProfileContradiction
import Mathlib.Tactic

/-!
# Exhaust all eight source retained-bit profiles

For a three-whole-cube star with distinct owners x,y,z, assume all four
centres are second-layer support-two.

The source retained code on x,y,z is one of eight Boolean profiles.

* 000 and 111 are excluded by the source-extreme profile contradictions.
* Every profile with exactly one true bit is a coordinate permutation of 100.
* Every profile with exactly one false bit is a coordinate permutation of 011
  (equivalently 110 after relabelling).

The mixed-profile contradiction theorems use the support-two source itself to
obtain the required one-step closeness, so no global-order extreme,
projected-loss hypothesis, or one-layer active-colour bound is needed here.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_threeWholeCube_allSupportTwo_profile_exhaustion
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
    {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂)
    (hc13 : c₁ ≠ c₃)
    (hc23 : c₂ ≠ c₃)
    (hactive :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R v = {c₁,c₂,c₃})
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
    (hvSecond :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam v) t = n - 2)
    (hs1Second :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam s₁) t = n - 2)
    (hs2Second :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam s₂) t = n - 2)
    (hs3Second :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam s₃) t = n - 2)
    (hvSupport :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam v) t) = 2)
    (hs1Support :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam s₁) t) = 2)
    (hs2Support :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam s₂) t) = 2)
    (hs3Support :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam s₃) t) = 2) :
    False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn3 : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam

  have hactive' : retainedActive R v = {c₁,c₂,c₃} := by
    simpa [R] using hactive

  have hc1 : retainedBit R v c₁ = false ∨ retainedBit R v c₁ = true := by
    cases h : retainedBit R v c₁ <;> simp [h]
  have hc2 : retainedBit R v c₂ = false ∨ retainedBit R v c₂ = true := by
    cases h : retainedBit R v c₂ <;> simp [h]
  have hc3 : retainedBit R v c₃ = false ∨ retainedBit R v c₃ = true := by
    cases h : retainedBit R v c₃ <;> simp [h]

  rcases hc1 with hc1F | hc1T <;>
    rcases hc2 with hc2F | hc2T <;>
    rcases hc3 with hc3F | hc3T

  · exact source_000_profile_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc12 hc13 hc23
      hactive h₁ h₂ h₃
      hs1Second hs2Second hs3Second
      hs1Support hs2Support hs3Support
      (by simpa [R] using hc1F)
      (by simpa [R] using hc2F)
      (by simpa [R] using hc3F)

  · have hactive₃ :
      retainedActive R v = {c₃,c₁,c₂} := by
      calc
        retainedActive R v = {c₁,c₂,c₃} := hactive'
        _ = {c₃,c₁,c₂} := by
          ext q
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
    exact source_100_profile_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc13.symm hc23.symm hc12
      (by simpa [R] using hactive₃)
      h₃ h₁ h₂
      hvSecond hs1Second hs2Second
      hvSupport hs1Support hs2Support
      (by simpa [R] using hc3T)
      (by simpa [R] using hc1F)
      (by simpa [R] using hc2F)

  · have hactive₂ :
      retainedActive R v = {c₂,c₁,c₃} := by
      calc
        retainedActive R v = {c₁,c₂,c₃} := hactive'
        _ = {c₂,c₁,c₃} := by
          ext q
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
    exact source_100_profile_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc12.symm hc23 hc13
      (by simpa [R] using hactive₂)
      h₂ h₁ h₃
      hvSecond hs1Second hs3Second
      hvSupport hs1Support hs3Support
      (by simpa [R] using hc2T)
      (by simpa [R] using hc1F)
      (by simpa [R] using hc3F)

  · exact source_011_profile_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc12 hc13 hc23
      hactive h₁ h₂ h₃
      hvSecond hs2Second hs3Second
      hvSupport hs2Support hs3Support
      (by simpa [R] using hc1F)
      (by simpa [R] using hc2T)
      (by simpa [R] using hc3T)

  · exact source_100_profile_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc12 hc13 hc23
      hactive h₁ h₂ h₃
      hvSecond hs2Second hs3Second
      hvSupport hs2Support hs3Support
      (by simpa [R] using hc1T)
      (by simpa [R] using hc2F)
      (by simpa [R] using hc3F)

  · have hactive₂ :
      retainedActive R v = {c₂,c₁,c₃} := by
      simpa [Finset.insert_comm, Finset.insert_left_comm, Finset.insert_assoc]
        using hactive'
    exact source_011_profile_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc12.symm hc23 hc13
      (by simpa [R] using hactive₂)
      h₂ h₁ h₃
      hvSecond hs1Second hs3Second
      hvSupport hs1Support hs3Support
      (by simpa [R] using hc2F)
      (by simpa [R] using hc1T)
      (by simpa [R] using hc3T)

  · have hactive₃ :
      retainedActive R v = {c₃,c₁,c₂} := by
      simpa [Finset.insert_comm, Finset.insert_left_comm, Finset.insert_assoc]
        using hactive'
    exact source_011_profile_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc13.symm hc23.symm hc12
      (by simpa [R] using hactive₃)
      h₃ h₁ h₂
      hvSecond hs1Second hs2Second
      hvSupport hs1Support hs2Support
      (by simpa [R] using hc3F)
      (by simpa [R] using hc1T)
      (by simpa [R] using hc2T)

  · exact source_111_profile_supportTwo_impossible
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
      hc12 hc13 hc23
      hactive h₁ h₂ h₃
      hs1Second hs2Second hs3Second
      hs1Support hs2Support hs3Support
      (by simpa [R] using hc1T)
      (by simpa [R] using hc2T)
      (by simpa [R] using hc3T)

#print axioms planar_threeWholeCube_allSupportTwo_profile_exhaustion

end ProjectionOrdered
end JSP000404Research
