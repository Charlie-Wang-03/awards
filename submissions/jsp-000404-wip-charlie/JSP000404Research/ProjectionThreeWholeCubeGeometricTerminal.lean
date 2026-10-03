import JSP000404Research.ProjectionThreeWholeCubeSharpSupportTerminal
import JSP000404Research.ProjectionThreeWholeCubeUnitTransitions
import JSP000404Research.FourSupportTwoDerangement
import Mathlib.Tactic

/-!
# Geometric terminal for the saturated four-vertex whole-cube core

Combine the sharp support terminal with the new palette-free four-support-two
derangement reduction.

For n >= 4 a saturated three-whole-cube star has exactly two possible forms:

1. all four vertices are support-two, in which case their four forced
   delta-small pairs form one of the nine K4 derangement patterns;
2. there is one support-one global order extreme, the other three vertices are
   support-two, all four retained palettes are one common consecutive triple,
   and every support-two vertex has a unit transition certificate.

Thus the unresolved four-vertex obstruction is reduced to one finite
palette-free nine-state branch and one highly rigid unique-support-one branch.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_threeWholeCubePartners_geometric_support_terminal
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
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
    (
      (
        (∀ q : ProjectionOrdered V,
          q ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) →
          positiveSupport (centreQuotient (Cfam q) t) = 2)
        ∧
        FourSupportTwoDerangementPattern9
          (reindexedPoint p) delta lam v s₁ s₂ s₃
      )
      ∨
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
              H.qe = 1)
    ) := by
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
  · left
    refine ⟨hall,?_⟩
    have hvSupport :
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

    have hcapR : AngleCap (reindexedPoint p) lam := by
      intro a b c hab hac hbc
      exact hcap a.toOriginal b.toOriginal c.toOriginal
        (by
          intro h
          apply hab
          exact ProjectionOrdered.toOriginal_injective h)
        (by
          intro h
          apply hac
          exact ProjectionOrdered.toOriginal_injective h)
        (by
          intro h
          apply hbc
          exact ProjectionOrdered.toOriginal_injective h)

    exact four_supportTwo_secondLayer_reduce_to_derangement_nine
      (reindexedPoint_injective hp)
      hcapR (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam Cfam
      hvs1 hvs2 hvs3 hs12 hs13 hs23
      hvSecond hs1Second hs2Second hs3Second
      hvSupport hs1Support hs2Support hs3Support

  · right
    obtain ⟨o,hoMem,hoOne,hoExtreme,hothers,
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

#print axioms planar_threeWholeCubePartners_geometric_support_terminal

end ProjectionOrdered
end JSP000404Research
