import JSP000404Research.ProjectionThreeWholeCubeSharpSupportTerminal
import JSP000404Research.ProjectionThreeWholeCubeAllSupportTwoProfileExhaustion
import JSP000404Research.ProjectionThreeWholeCubeUniqueSupportOneContradiction
import Mathlib.Tactic

/-!
# Saturated three-whole-cube four-vertex core is impossible

The sharp support terminal has exactly two branches.

* all four centres support-two;
* one globally extreme support-one centre and three support-two centres.

The first branch is impossible by eight-profile exhaustion at the whole-cube
source.  The second branch is impossible by the unique-support-one profile
contradiction.

Thus the saturated four-vertex three-whole-cube core cannot occur.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_threeWholeCube_saturated_four_vertex_impossible
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
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {v s₁ s₂ s₃ : ProjectionOrdered V}
    (hvs1 : v ≠ s₁)
    (hvs2 : v ≠ s₂)
    (hvs3 : v ≠ s₃)
    (hs12 : s₁ ≠ s₂)
    (hs13 : s₁ ≠ s₃)
    (hs23 : s₂ ≠ s₃)
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
    (hvLoss :
      v ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hs1Loss :
      s₁ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hs2Loss :
      s₂ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hs3Loss :
      s₃ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hvSecond : centreExponent (Cfam v) t = n - 2)
    (hs1Second : centreExponent (Cfam s₁) t = n - 2)
    (hs2Second : centreExponent (Cfam s₂) t = n - 2)
    (hs3Second : centreExponent (Cfam s₃) t = n - 2)
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
      WholeCubeQTPair R s₃ v c₃) :
    False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp

  have hterm :=
    planar_threeWholeCubePartners_sharp_support_terminal
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
      hvs1 hvs2 hvs3 hs12 hs13 hs23
      hc12 hc13 hc23 hactive
      hvLoss hs1Loss hs2Loss hs3Loss
      hvSecond hs1Second hs2Second hs3Second
      h₁ h₂ h₃

  rcases hterm with hall | huniq

  · have hvSupport :
        positiveSupport (centreQuotient (Cfam v) t) = 2 :=
      hall v (by simp)
    have hs1Support :
        positiveSupport (centreQuotient (Cfam s₁) t) = 2 :=
      hall s₁ (by simp)
    have hs2Support :
        positiveSupport (centreQuotient (Cfam s₂) t) = 2 :=
      hall s₂ (by simp)
    have hs3Support :
        positiveSupport (centreQuotient (Cfam s₃) t) = 2 :=
      hall s₃ (by simp)
    exact planar_threeWholeCube_allSupportTwo_profile_exhaustion
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
      hc12 hc13 hc23 hactive h₁ h₂ h₃
      hvSecond hs1Second hs2Second hs3Second
      hvSupport hs1Support hs2Support hs3Support

  · obtain ⟨o,hoMem,_hoOne,hoExtreme,hothers,
      _m,_hpalV,_hpalS1,_hpalS2,_hpalS3⟩ := huniq
    exact planar_threeWholeCube_uniqueSupportOne_impossible
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
      hvs1 hvs2 hvs3 hs12 hs13 hs23
      hc12 hc13 hc23
      hactive h₁ h₂ h₃
      hvSecond hs1Second hs2Second hs3Second
      hoMem hoExtreme hothers

#print axioms planar_threeWholeCube_saturated_four_vertex_impossible

end ProjectionOrdered
end JSP000404Research
