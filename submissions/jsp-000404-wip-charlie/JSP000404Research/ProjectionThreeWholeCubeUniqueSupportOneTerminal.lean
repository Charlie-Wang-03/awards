import JSP000404Research.ProjectionThreeWholeCubeUniqueSupportOneContradiction
import JSP000404Research.ProjectionThreeWholeCubeSharpSupportTerminal
import JSP000404Research.ProjectionThreeWholeCubeUnitTransitions
import JSP000404Research.ProjectionThreeWholeCubeAllSupportTwoProfileExhaustion
import Mathlib.Tactic

/-!
# Saturated four-vertex terminal: unique support-one only

The sharp support terminal has two branches:

1. all four centres are support-two;
2. exactly one centre is support-one, globally order-extreme, the other three
   are support-two, and all four retained palettes are the same consecutive
   triple.

The all-support-two branch is now impossible by exhaustive analysis of the
eight retained-bit profiles at the whole-cube source.  Therefore only the
unique-support-one branch survives.  The existing unit-transition theorem then
upgrades all three support-two centres to qe=1 certificates.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_threeWholeCubePartners_uniqueSupportOne_terminal
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
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    ∃ o : ProjectionOrdered V,
      o ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) ∧
      positiveSupport (centreQuotient (Cfam o) t) = 1 ∧
      GlobalOrderExtreme o ∧
      (∀ q : ProjectionOrdered V,
        q ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) →
        q ≠ o →
        positiveSupport (centreQuotient (Cfam q) t) = 2) ∧
      ∃ m : ℕ,
        (retainedActive R v).map Fin.valEmbedding = threeNatInterval m ∧
        (retainedActive R s₁).map Fin.valEmbedding = threeNatInterval m ∧
        (retainedActive R s₂).map Fin.valEmbedding = threeNatInterval m ∧
        (retainedActive R s₃).map Fin.valEmbedding = threeNatInterval m ∧
        (∀ q : ProjectionOrdered V,
          q ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) →
          q ≠ o →
          ∃ H : HighExponentTransitionIntervalCertificate
              (reindexedPoint_injective hp) t q (Cfam q),
            H.qe = 1) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam

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
    exact False.elim
      (planar_threeWholeCube_allSupportTwo_profile_exhaustion
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
        hc12 hc13 hc23 hactive h₁ h₂ h₃
        hvSecond hs1Second hs2Second hs3Second
        hvSupport hs1Support hs2Support hs3Support)

  · obtain ⟨o,hoMem,hoOne,hoExtreme,hothers,
      m,hpalV,hpalS1,hpalS2,hpalS3⟩ := huniq
    have hunit :=
      planar_threeWholeCube_uniqueSupportOne_others_unitTransition
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
        hvs1 hvs2 hvs3 hs12 hs13 hs23
        hc12 hc13 hc23 hactive
        hvLoss hs1Loss hs2Loss hs3Loss
        hvSecond hs1Second hs2Second hs3Second
        h₁ h₂ h₃
        hoMem hoExtreme hothers
        hpalV hpalS1 hpalS2 hpalS3
    exact ⟨o,hoMem,hoOne,hoExtreme,hothers,
      m,hpalV,hpalS1,hpalS2,hpalS3,hunit⟩

/-- The four-centre loss star cannot occur in the planar lower branch.
This discharges the unique-support-one extreme terminal using the previously
proved source and partner extreme profile contradictions. -/
theorem planar_threeWholeCubePartners_lossStar_impossible
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
      WholeCubeQTPair R s₃ v c₃) : False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hterm :=
    planar_threeWholeCubePartners_uniqueSupportOne_terminal
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
      hvs1 hvs2 hvs3 hs12 hs13 hs23
      hc12 hc13 hc23 hactive
      hvLoss hs1Loss hs2Loss hs3Loss
      hvSecond hs1Second hs2Second hs3Second
      h₁ h₂ h₃
  obtain ⟨o, hoMem, _, hoExtreme, hothers, _, _, _, _, _, _⟩ :=
    hterm
  exact planar_threeWholeCube_uniqueSupportOne_impossible
    hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
    hvs1 hvs2 hvs3 hs12 hs13 hs23
    hc12 hc13 hc23 hactive h₁ h₂ h₃
    hvSecond hs1Second hs2Second hs3Second
    hoMem hoExtreme hothers

#print axioms planar_threeWholeCubePartners_lossStar_impossible

#print axioms planar_threeWholeCubePartners_uniqueSupportOne_terminal

end ProjectionOrdered
end JSP000404Research
