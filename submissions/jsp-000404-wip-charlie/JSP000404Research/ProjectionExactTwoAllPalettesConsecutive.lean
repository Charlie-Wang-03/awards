import JSP000404Research.ProjectionSupportOneConsecutivePalette
import JSP000404Research.ProjectionUnitSupportTwoConsecutiveBands
import Mathlib.Tactic

/-!
# All four palettes are consecutive in the exact-two support terminal
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem exactTwo_support_four_projectedLoss_palettes_consecutive
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
    {o₁ o₂ s₁ s₂ : ProjectionOrdered V}
    (ho1Loss :
      o₁ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (ho2Loss :
      o₂ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hs1Loss :
      s₁ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hs2Loss :
      s₂ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (ho1Second : centreExponent (C o₁) t = n - 2)
    (ho2Second : centreExponent (C o₂) t = n - 2)
    (hs1Second : centreExponent (C s₁) t = n - 2)
    (hs2Second : centreExponent (C s₂) t = n - 2)
    (ho1Support :
      positiveSupport (centreQuotient (C o₁) t) = 1)
    (ho2Support :
      positiveSupport (centreQuotient (C o₂) t) = 1)
    (hs1Support :
      positiveSupport (centreQuotient (C s₁) t) = 2)
    (hs2Support :
      positiveSupport (centreQuotient (C s₂) t) = 2)
    (cert₁ :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t s₁ (C s₁))
    (cert₂ :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t s₂ (C s₂))
    (hqe1 : cert₁.qe = 1)
    (hqe2 : cert₂.qe = 1) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    ∃ mo₁ mo₂ ms₁ ms₂ : ℕ,
      (retainedActive R o₁).map Fin.valEmbedding =
        {mo₁,mo₁+1,mo₁+2} ∧
      (retainedActive R o₂).map Fin.valEmbedding =
        {mo₂,mo₂+1,mo₂+2} ∧
      (retainedActive R s₁).map Fin.valEmbedding =
        {ms₁,ms₁+1,ms₁+2} ∧
      (retainedActive R s₂).map Fin.valEmbedding =
        {ms₂,ms₂+1,ms₂+2} := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam

  obtain ⟨mo₁,hpo1⟩ :=
    planar_projectedLoss_supportOne_retainedPalette_consecutive
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      C o₁ ho1Loss ho1Second ho1Support
  obtain ⟨mo₂,hpo2⟩ :=
    planar_projectedLoss_supportOne_retainedPalette_consecutive
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      C o₂ ho2Loss ho2Second ho2Support
  obtain ⟨ms₁,hps1⟩ :=
    planar_projectedLoss_unitSupportTwo_retainedPalette_consecutive
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      C s₁ hs1Loss hs1Second hs1Support cert₁ hqe1
  obtain ⟨ms₂,hps2⟩ :=
    planar_projectedLoss_unitSupportTwo_retainedPalette_consecutive
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      C s₂ hs2Loss hs2Second hs2Support cert₂ hqe2

  exact ⟨mo₁,mo₂,ms₁,ms₂,
    by simpa [R] using hpo1,
    by simpa [R] using hpo2,
    by simpa [R] using hps1,
    by simpa [R] using hps2⟩

#print axioms exactTwo_support_four_projectedLoss_palettes_consecutive

end ProjectionOrdered
end JSP000404Research
