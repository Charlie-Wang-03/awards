import JSP000404Research.ProjectionExactTwoAllPalettesConsecutive
import JSP000404Research.FourConsecutiveLossPaletteHelly
import JSP000404Research.ThreeColourPaletteFiveEnvelope
import Mathlib.Tactic

/-!
# Five-band retained-palette envelope in the exact-two Q/T/T/T terminal

All four projected-loss second-layer palettes are consecutive triples.  Every
pair of loss vertices is joined by a retained edge, hence the four palettes
pairwise intersect.  Therefore all four palettes lie inside one block of five
consecutive retained labels.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem exactTwo_support_four_projectedLoss_five_band_envelope
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
    ∃ m : ℕ,
      (retainedActive R o₁).map Fin.valEmbedding ⊆ fiveNatInterval m ∧
      (retainedActive R o₂).map Fin.valEmbedding ⊆ fiveNatInterval m ∧
      (retainedActive R s₁).map Fin.valEmbedding ⊆ fiveNatInterval m ∧
      (retainedActive R s₂).map Fin.valEmbedding ⊆ fiveNatInterval m := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam
  let exponent := planarCentreExponent hp C

  obtain ⟨mo₁,mo₂,ms₁,ms₂,
      hpo1,hpo2,hps1,hps2⟩ :=
    exactTwo_support_four_projectedLoss_palettes_consecutive
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam C
      ho1Loss ho2Loss hs1Loss hs2Loss
      ho1Second ho2Second hs1Second hs2Second
      ho1Support ho2Support hs1Support hs2Support
      cert₁ cert₂ hqe1 hqe2

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam C
  have hexp : ∀ q, exponent q ≤ n := by
    intro q
    exact Nat.le_of_lt
      (by simpa [exponent] using hprofile.1 q)
  have hone :
      ∀ q, (active R q).card ≤ n - exponent q + 1 := by
    intro q
    simpa [R,exponent] using hprofile.2 q

  have hi12 :=
    OrderedEdgeColoring.mapped_palette_intersection_of_retained_intersection
      R
      (by simpa [R,threeNatInterval] using hpo1)
      (by simpa [R,threeNatInterval] using hpo2)
      (OrderedEdgeColoring.projectedLoss_pair_retainedActive_inter_nonempty
        R exponent hexp hone ho12
        (by simpa [R,exponent] using ho1Loss)
        (by simpa [R,exponent] using ho2Loss))
  have hi1s1 :=
    OrderedEdgeColoring.mapped_palette_intersection_of_retained_intersection
      R
      (by simpa [R,threeNatInterval] using hpo1)
      (by simpa [R,threeNatInterval] using hps1)
      (OrderedEdgeColoring.projectedLoss_pair_retainedActive_inter_nonempty
        R exponent hexp hone ho1s1
        (by simpa [R,exponent] using ho1Loss)
        (by simpa [R,exponent] using hs1Loss))
  have hi1s2 :=
    OrderedEdgeColoring.mapped_palette_intersection_of_retained_intersection
      R
      (by simpa [R,threeNatInterval] using hpo1)
      (by simpa [R,threeNatInterval] using hps2)
      (OrderedEdgeColoring.projectedLoss_pair_retainedActive_inter_nonempty
        R exponent hexp hone ho1s2
        (by simpa [R,exponent] using ho1Loss)
        (by simpa [R,exponent] using hs2Loss))
  have hi2s1 :=
    OrderedEdgeColoring.mapped_palette_intersection_of_retained_intersection
      R
      (by simpa [R,threeNatInterval] using hpo2)
      (by simpa [R,threeNatInterval] using hps1)
      (OrderedEdgeColoring.projectedLoss_pair_retainedActive_inter_nonempty
        R exponent hexp hone ho2s1
        (by simpa [R,exponent] using ho2Loss)
        (by simpa [R,exponent] using hs1Loss))
  have hi2s2 :=
    OrderedEdgeColoring.mapped_palette_intersection_of_retained_intersection
      R
      (by simpa [R,threeNatInterval] using hpo2)
      (by simpa [R,threeNatInterval] using hps2)
      (OrderedEdgeColoring.projectedLoss_pair_retainedActive_inter_nonempty
        R exponent hexp hone ho2s2
        (by simpa [R,exponent] using ho2Loss)
        (by simpa [R,exponent] using hs2Loss))
  have his12 :=
    OrderedEdgeColoring.mapped_palette_intersection_of_retained_intersection
      R
      (by simpa [R,threeNatInterval] using hps1)
      (by simpa [R,threeNatInterval] using hps2)
      (OrderedEdgeColoring.projectedLoss_pair_retainedActive_inter_nonempty
        R exponent hexp hone hs12
        (by simpa [R,exponent] using hs1Loss)
        (by simpa [R,exponent] using hs2Loss))

  obtain ⟨m,hm1,hm2,hm3,hm4⟩ :=
    four_threeNatIntervals_pairwise_intersect_five_envelope
      hi12 hi1s1 hi1s2 hi2s1 hi2s2 his12

  refine ⟨m,?_,?_,?_,?_⟩
  · rw [hpo1]
    exact hm1
  · rw [hpo2]
    exact hm2
  · rw [hps1]
    exact hm3
  · rw [hps2]
    exact hm4

#print axioms exactTwo_support_four_projectedLoss_five_band_envelope

end ProjectionOrdered
end JSP000404Research
