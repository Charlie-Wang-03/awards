import JSP000404Research.ProjectionExactTwoFiveBandEnvelope
import JSP000404Research.ProjectionFiveBandDirectionWindow
import Mathlib.Tactic

/-!
# Exact-two four-point K4 direction window

The exact-two Q/T/T/T palette terminal confines all four retained palettes to
one five-band envelope.  Every pair of projected-loss vertices is connected by
a retained edge.  Therefore all six oriented pair direction values lie in one
common normalized interval [m,m+5).
-/

namespace JSP000404Research
namespace ProjectionOrdered

def PairValueInFiveWindow
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (m : ℕ) (u v : V) : Prop :=
  (u < v ∧
      (m : ℝ) ≤ D.value u v ∧
      D.value u v < (m : ℝ) + 5)
  ∨
  (v < u ∧
      (m : ℝ) ≤ D.value v u ∧
      D.value v u < (m : ℝ) + 5)

theorem projectedLoss_pair_in_five_window_of_both_palettes
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    {n m : ℕ}
    (hwidth : width < (n + 1 : ℕ))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q,
        (OrderedEdgeColoring.active
          (DirectionData.standardResidualColoring D n hwidth) q).card
          ≤ n - exponent q + 1)
    {u v : V}
    (huv : u ≠ v)
    (huLoss :
      u ∈ OrderedEdgeColoring.projectedLossVertices
        (DirectionData.standardResidualColoring D n hwidth) exponent)
    (hvLoss :
      v ∈ OrderedEdgeColoring.projectedLossVertices
        (DirectionData.standardResidualColoring D n hwidth) exponent)
    (huPalette :
      (OrderedEdgeColoring.retainedActive
        (DirectionData.standardResidualColoring D n hwidth) u).map
          Fin.valEmbedding
        ⊆ fiveNatInterval m)
    (hvPalette :
      (OrderedEdgeColoring.retainedActive
        (DirectionData.standardResidualColoring D n hwidth) v).map
          Fin.valEmbedding
        ⊆ fiveNatInterval m) :
    PairValueInFiveWindow D m u v := by
  rcases lt_or_gt_of_ne huv with huvlt | hvult
  · left
    refine ⟨huvlt,?_⟩
    exact DirectionData.projectedLoss_pair_value_mem_five_window
      D hwidth exponent hexp honeLoss
      huvlt huLoss huPalette
  · right
    refine ⟨hvult,?_⟩
    exact DirectionData.projectedLoss_pair_value_mem_five_window
      D hwidth exponent hexp honeLoss
      hvult hvLoss hvPalette

theorem exactTwo_support_four_projectedLoss_K4_five_direction_window
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
    (ho12 : o₁ ≠ o₂)
    (ho1s1 : o₁ ≠ s₁) (ho1s2 : o₁ ≠ s₂)
    (ho2s1 : o₂ ≠ s₁) (ho2s2 : o₂ ≠ s₂)
    (hs12 : s₁ ≠ s₂)
    (ho1Loss :
      o₁ ∈ OrderedEdgeColoring.projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (ho2Loss :
      o₂ ∈ OrderedEdgeColoring.projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hs1Loss :
      s₁ ∈ OrderedEdgeColoring.projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hs2Loss :
      s₂ ∈ OrderedEdgeColoring.projectedLossVertices
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
    let htpos : 0 < t :=
      sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
    let D :=
      genericDirectionData_sendov hp hcap htpos hlam
    ∃ m : ℕ,
      PairValueInFiveWindow D m o₁ o₂ ∧
      PairValueInFiveWindow D m o₁ s₁ ∧
      PairValueInFiveWindow D m o₁ s₂ ∧
      PairValueInFiveWindow D m o₂ s₁ ∧
      PairValueInFiveWindow D m o₂ s₂ ∧
      PairValueInFiveWindow D m s₁ s₂ := by
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
  let R :=
    DirectionData.standardResidualColoring D n hwidth
  let exponent := planarCentreExponent hp C

  have hReq :
      R =
      planarStandardResidualColoring
        hp hcap hn1 hdelta0 hdelta1 ht hlam := by
    rfl

  obtain ⟨m,ho1Pal,ho2Pal,hs1Pal,hs2Pal⟩ :=
    exactTwo_support_four_projectedLoss_five_band_envelope
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam C
      ho12 ho1s1 ho1s2 ho2s1 ho2s2 hs12
      ho1Loss ho2Loss hs1Loss hs2Loss
      ho1Second ho2Second hs1Second hs2Second
      ho1Support ho2Support hs1Support hs2Support
      cert₁ cert₂ hqe1 hqe2

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap hn1 hdelta0 hdelta1 ht hlam C
  have hexp : ∀ q, exponent q ≤ n := by
    intro q
    exact Nat.le_of_lt
      (by simpa [exponent] using hprofile.1 q)
  have hone :
      ∀ q, (OrderedEdgeColoring.active R q).card
        ≤ n - exponent q + 1 := by
    intro q
    simpa [R,D,exponent] using hprofile.2 q

  have ho1Loss' :
      o₁ ∈ OrderedEdgeColoring.projectedLossVertices R exponent := by
    simpa [R,D,exponent] using ho1Loss
  have ho2Loss' :
      o₂ ∈ OrderedEdgeColoring.projectedLossVertices R exponent := by
    simpa [R,D,exponent] using ho2Loss
  have hs1Loss' :
      s₁ ∈ OrderedEdgeColoring.projectedLossVertices R exponent := by
    simpa [R,D,exponent] using hs1Loss
  have hs2Loss' :
      s₂ ∈ OrderedEdgeColoring.projectedLossVertices R exponent := by
    simpa [R,D,exponent] using hs2Loss

  have ho1Pal' :
      (OrderedEdgeColoring.retainedActive R o₁).map Fin.valEmbedding
        ⊆ fiveNatInterval m := by
    simpa [R,D] using ho1Pal
  have ho2Pal' :
      (OrderedEdgeColoring.retainedActive R o₂).map Fin.valEmbedding
        ⊆ fiveNatInterval m := by
    simpa [R,D] using ho2Pal
  have hs1Pal' :
      (OrderedEdgeColoring.retainedActive R s₁).map Fin.valEmbedding
        ⊆ fiveNatInterval m := by
    simpa [R,D] using hs1Pal
  have hs2Pal' :
      (OrderedEdgeColoring.retainedActive R s₂).map Fin.valEmbedding
        ⊆ fiveNatInterval m := by
    simpa [R,D] using hs2Pal

  refine ⟨m,?_,?_,?_,?_,?_,?_⟩
  · exact projectedLoss_pair_in_five_window_of_both_palettes
      D hwidth exponent hexp hone
      ho12 ho1Loss' ho2Loss' ho1Pal' ho2Pal'
  · exact projectedLoss_pair_in_five_window_of_both_palettes
      D hwidth exponent hexp hone
      ho1s1 ho1Loss' hs1Loss' ho1Pal' hs1Pal'
  · exact projectedLoss_pair_in_five_window_of_both_palettes
      D hwidth exponent hexp hone
      ho1s2 ho1Loss' hs2Loss' ho1Pal' hs2Pal'
  · exact projectedLoss_pair_in_five_window_of_both_palettes
      D hwidth exponent hexp hone
      ho2s1 ho2Loss' hs1Loss' ho2Pal' hs1Pal'
  · exact projectedLoss_pair_in_five_window_of_both_palettes
      D hwidth exponent hexp hone
      ho2s2 ho2Loss' hs2Loss' ho2Pal' hs2Pal'
  · exact projectedLoss_pair_in_five_window_of_both_palettes
      D hwidth exponent hexp hone
      hs12 hs1Loss' hs2Loss' hs1Pal' hs2Pal'

#print axioms projectedLoss_pair_in_five_window_of_both_palettes
#print axioms exactTwo_support_four_projectedLoss_K4_five_direction_window

end ProjectionOrdered
end JSP000404Research
