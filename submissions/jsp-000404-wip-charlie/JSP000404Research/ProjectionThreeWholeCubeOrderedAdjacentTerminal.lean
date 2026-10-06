import JSP000404Research.ProjectionFourSupportTwoOrderedAdjacentFromExtreme
import JSP000404Research.ThreeWholeCubeGlobalExtreme
import Mathlib.Tactic

/-!
# Ordered adjacent terminal for the all-support-two whole-cube star

The whole-cube retained-code star is used only to produce a global order
extreme among the four vertices.  Once that extreme is known, the checked
lightweight terminal

  global extreme
  + four projected-loss second-layer support-two centres
  -> sorted a<b<c<d
  -> unique ordered-adjacent support-two pattern

does the remaining geometry.

This file therefore isolates the genuinely whole-cube-specific bridge from
the already kernel-checked ordered-adjacent terminal.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_threeWholeCube_allSupportTwo_ordered_adjacent_terminal
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
    (hs12 : s₁ ≠ s₂) (hs13 : s₁ ≠ s₃) (hs23 : s₂ ≠ s₃)
    {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂) (hc13 : c₁ ≠ c₃) (hc23 : c₂ ≠ c₃)
    (hactive :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R v = {c₁,c₂,c₃})
    (hvLoss :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      v ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent (t := t) hp Cfam))
    (hs1Loss :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      s₁ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent (t := t) hp Cfam))
    (hs2Loss :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      s₂ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent (t := t) hp Cfam))
    (hs3Loss :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      s₃ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent (t := t) hp Cfam))
    (hvSecond : centreExponent (Cfam v) t = n - 2)
    (hs1Second : centreExponent (Cfam s₁) t = n - 2)
    (hs2Second : centreExponent (Cfam s₂) t = n - 2)
    (hs3Second : centreExponent (Cfam s₃) t = n - 2)
    (hvSupport : positiveSupport (centreQuotient (Cfam v) t) = 2)
    (hs1Support : positiveSupport (centreQuotient (Cfam s₁) t) = 2)
    (hs2Support : positiveSupport (centreQuotient (Cfam s₂) t) = 2)
    (hs3Support : positiveSupport (centreQuotient (Cfam s₃) t) = 2)
    (h₁ :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₁ v c₁)
    (h₂ :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₂ v c₂)
    (h₃ :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₃ v c₃) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    ∃ a b c d : ProjectionOrdered V,
      ({a,b,c,d} : Finset (ProjectionOrdered V)) = {v,s₁,s₂,s₃} ∧
      a < b ∧ b < c ∧ c < d ∧
      FourSupportTwoOrderedAdjacentPattern
        (reindexedPoint p) delta lam a b c d := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith

  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent (t := t) hp Cfam

  have hexp : ∀ q, exponent q ≤ n := by
    exact planarCentreExponent_le_n_light
      hp hn1 hdelta0 hdelta1 ht Cfam

  have hone :
      ∀ q, (active R q).card ≤ n - exponent q + 1 := by
    intro q
    simpa [R, exponent, planarCentreExponent,
      planarStandardResidualColoring] using
      (planarStandardResidual_active_card_le_oneLayer
        hp hcap hn1 hdelta0 hdelta1 ht hlam q (Cfam q))

  have hc1V : c₁ ∈ retainedActive R v := by
    rw [hactive]
    simp
  have hc2V : c₂ ∈ retainedActive R v := by
    rw [hactive]
    simp
  have hc3V : c₃ ∈ retainedActive R v := by
    rw [hactive]
    simp

  have hextreme :=
    threeWholeCubePartners_has_global_extreme
      R exponent hexp hone
      hc12 hc13 hc23
      (by simpa [R, exponent] using hvLoss)
      (by simpa [R, exponent] using hs1Loss)
      (by simpa [R, exponent] using hs2Loss)
      (by simpa [R, exponent] using hs3Loss)
      (by simpa [R] using hactive)
      (by simpa [R] using h₁)
      (by simpa [R] using h₂)
      (by simpa [R] using h₃)

  exact
    planar_fourSupportTwo_of_globalExtreme_ordered_adjacent_terminal
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
      hvs1 hvs2 hvs3 hs12 hs13 hs23
      hvLoss hs1Loss hs2Loss hs3Loss
      hvSecond hs1Second hs2Second hs3Second
      hvSupport hs1Support hs2Support hs3Support
      (by simpa [FourPointGlobalExtreme] using hextreme)

#print axioms planar_threeWholeCube_allSupportTwo_ordered_adjacent_terminal

end ProjectionOrdered
end JSP000404Research
