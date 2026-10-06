import JSP000404Research.ProjectionThreeWholeCubeSaturatedContradiction
import JSP000404Research.ResidualWholeCubePartnerDistinct
import JSP000404Research.ResidualWholeCubeDiscoveryRank
import Mathlib.Tactic

/-!
# Full whole-cube discovery is impossible in the planar second layer

For a projected-loss second-layer source v, the retained-active palette has
cardinality three.  Suppose every retained coordinate has already acquired a
projected-loss second-layer WholeCubeQTPair partner.

Enumerating the three retained coordinates gives three pairwise-distinct
owners c1,c2,c3.  Whole-cube coordinate uniqueness forces the corresponding
partners s1,s2,s3 to be pairwise distinct, and active translated slices force
each partner to differ from v.  The resulting configuration is exactly the
saturated four-vertex whole-cube core, which is impossible.

This is the bridge needed to turn the numerical discovery rank into a genuine
terminal: rank zero is geometrically unreachable.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_secondLayer_full_wholeCube_discovery_impossible
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
    {v : ProjectionOrdered V}
    (hvLoss :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      v ∈ projectedLossVertices R (planarCentreExponent hp Cfam))
    (hvSecond : centreExponent (Cfam v) t = n - 2)
    (hregistry :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      ∀ d,
        d ∈ retainedActive R v →
        ∃ s : ProjectionOrdered V,
          s ∈ projectedLossVertices R (planarCentreExponent hp Cfam) ∧
          centreExponent (Cfam s) t = n - 2 ∧
          WholeCubeQTPair R s v d) :
    False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn3 : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent :=
    planarCentreExponent (t := t) hp Cfam

  have hvLoss' :
      v ∈ projectedLossVertices R exponent := by
    simpa [R, exponent] using hvLoss
  have hvSecond' : exponent v = n - 2 := by
    simpa [exponent, planarCentreExponent] using hvSecond

  have hcard :
      (retainedActive R v).card = 3 :=
    secondLayerLoss_retainedActive_card_eq_three
      R exponent hvLoss' hvSecond'

  obtain ⟨c₁,c₂,c₃,hc12,hc13,hc23,hactive⟩ :=
    Finset.card_eq_three.mp hcard

  have hc1V : c₁ ∈ retainedActive R v := by
    rw [hactive]
    simp
  have hc2V : c₂ ∈ retainedActive R v := by
    rw [hactive]
    simp
  have hc3V : c₃ ∈ retainedActive R v := by
    rw [hactive]
    simp

  obtain ⟨s₁,hs1Loss,hs1Second,h₁⟩ :=
    hregistry c₁ (by simpa [R] using hc1V)
  obtain ⟨s₂,hs2Loss,hs2Second,h₂⟩ :=
    hregistry c₂ (by simpa [R] using hc2V)
  obtain ⟨s₃,hs3Loss,hs3Second,h₃⟩ :=
    hregistry c₃ (by simpa [R] using hc3V)

  have hvs1 : v ≠ s₁ := by
    exact (wholeCubeQTPair_ne_of_active R hc1V h₁).symm
  have hvs2 : v ≠ s₂ := by
    exact (wholeCubeQTPair_ne_of_active R hc2V h₂).symm
  have hvs3 : v ≠ s₃ := by
    exact (wholeCubeQTPair_ne_of_active R hc3V h₃).symm

  have hs12 : s₁ ≠ s₂ :=
    wholeCubeQTPair_partners_ne_of_coordinates_ne
      R hc1V hc2V hc12 h₁ h₂
  have hs13 : s₁ ≠ s₃ :=
    wholeCubeQTPair_partners_ne_of_coordinates_ne
      R hc1V hc3V hc13 h₁ h₃
  have hs23 : s₂ ≠ s₃ :=
    wholeCubeQTPair_partners_ne_of_coordinates_ne
      R hc2V hc3V hc23 h₂ h₃

  exact planar_threeWholeCube_saturated_four_vertex_impossible
    hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
    hvs1 hvs2 hvs3 hs12 hs13 hs23
    hc12 hc13 hc23
    (by simpa [R] using hactive)
    (by simpa [R, exponent] using hvLoss')
    (by simpa [R, exponent] using hs1Loss)
    (by simpa [R, exponent] using hs2Loss)
    (by simpa [R, exponent] using hs3Loss)
    hvSecond hs1Second hs2Second hs3Second
    (by simpa [R] using h₁)
    (by simpa [R] using h₂)
    (by simpa [R] using h₃)

#print axioms planar_secondLayer_full_wholeCube_discovery_impossible

end ProjectionOrdered
end JSP000404Research
