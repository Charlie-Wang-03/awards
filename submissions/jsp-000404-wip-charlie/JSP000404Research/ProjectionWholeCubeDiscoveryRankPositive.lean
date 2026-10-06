import JSP000404Research.ProjectionWholeCubeFullDiscoveryContradiction
import JSP000404Research.ResidualWholeCubeDiscoveryRank
import Mathlib.Tactic

/-!
# Positive lower bound for planar whole-cube discovery rank

The abstract discovery rank takes values 0,1,2,3.  In the genuine planar
second-layer branch, rank zero is impossible: discovering all three retained
coordinates would produce the saturated three-partner whole-cube core, which
has already been ruled out.

Consequently every finite set of genuinely discovered projected-loss
second-layer whole-cube coordinates has cardinality at most two, hence
discovery rank at least one.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_secondLayer_discovered_coordinates_card_le_two
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
    (hvSecond :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam v) t = n - 2)
    (coords : Finset (Fin n))
    (hcoords :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      coords ⊆ retainedActive R v)
    (hregistry :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      ∀ d,
        d ∈ coords →
        ∃ s : ProjectionOrdered V,
          s ∈ projectedLossVertices R (planarCentreExponent hp Cfam) ∧
          centreExponent (Cfam s) t = n - 2 ∧
          WholeCubeQTPair R s v d) :
    coords.card ≤ 2 := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent (t := t) hp Cfam

  have hvLoss' : v ∈ projectedLossVertices R exponent := by
    simpa [R, exponent] using hvLoss
  have hvSecond' : exponent v = n - 2 := by
    simpa [exponent, planarCentreExponent] using hvSecond
  have hcoords' : coords ⊆ retainedActive R v := by
    simpa [R] using hcoords

  have hactiveCard : (retainedActive R v).card = 3 :=
    secondLayerLoss_retainedActive_card_eq_three
      R exponent hvLoss' hvSecond'
  have hle3 : coords.card ≤ 3 := by
    exact (Finset.card_le_card hcoords').trans_eq hactiveCard

  by_contra hnot
  have hcard : coords.card = 3 := by omega
  have hEq : coords = retainedActive R v := by
    apply Finset.eq_of_subset_of_card_le hcoords'
    simpa [hcard, hactiveCard]

  apply planar_secondLayer_full_wholeCube_discovery_impossible
    hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
    hvLoss hvSecond
  intro d hd
  have hdCoords : d ∈ coords := by
    rw [hEq]
    exact hd
  exact hregistry d (by simpa [R] using hdCoords)

theorem planar_secondLayer_wholeCubeDiscoveryRank_pos
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
    (hvSecond :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam v) t = n - 2)
    (coords : Finset (Fin n))
    (hcoords :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      coords ⊆ retainedActive R v)
    (hregistry :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      ∀ d,
        d ∈ coords →
        ∃ s : ProjectionOrdered V,
          s ∈ projectedLossVertices R (planarCentreExponent hp Cfam) ∧
          centreExponent (Cfam s) t = n - 2 ∧
          WholeCubeQTPair R s v d) :
    1 ≤ wholeCubeDiscoveryRank coords := by
  have hcard :=
    planar_secondLayer_discovered_coordinates_card_le_two
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
      hvLoss hvSecond coords hcoords hregistry
  unfold wholeCubeDiscoveryRank
  omega

#print axioms planar_secondLayer_discovered_coordinates_card_le_two
#print axioms planar_secondLayer_wholeCubeDiscoveryRank_pos

end ProjectionOrdered
end JSP000404Research
