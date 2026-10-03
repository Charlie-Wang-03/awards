import JSP000404Research.FourSupportTwoDerangementExtremeMatrix
import JSP000404Research.ProjectionThreeWholeCubeSourceExtremeAngles
import Mathlib.Tactic

/-!
# The source cannot be the global extreme in the all-support-two terminal

Assume the three whole-cube partners have been named in increasing projection
order s1 < s2 < s3.  If the source v is a global minimum or maximum, the
whole-cube code star gives the corresponding strict sub-lambda angle matrix.

The palette-free all-support-two terminal gives one of the nine derangement
small-angle patterns.  The previous module proves that either source-extreme
matrix is incompatible with all nine patterns.

Hence, in the all-four-support-two saturated core, the guaranteed global
extreme cannot be the source (after ordering the three partners).  The
remaining extreme-partner case is the next finite geometric frontier.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_threeWholeCube_derangement_sourceGlobalMin_impossible
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
    (hpat :
      FourSupportTwoDerangementPattern9
        (reindexedPoint p) delta lam v s₁ s₂ s₃)
    (hmin :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ w : ProjectionOrdered V, w ≠ v → v < w)
    (hs12lt :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      s₁ < s₂)
    (hs23lt :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      s₂ < s₃) :
    False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam

  have hactive' : retainedActive R v = {c₁,c₂,c₃} := by
    simpa [R] using hactive
  have hc1V : c₁ ∈ retainedActive R v := by
    rw [hactive']
    simp
  have hc2V : c₂ ∈ retainedActive R v := by
    rw [hactive']
    simp
  have hc3V : c₃ ∈ retainedActive R v := by
    rw [hactive']
    simp

  have hmatrix :=
    threeWholeCube_source_globalMin_sameBand_angles
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam Cfam
      hvs1 hvs2 hvs3 hs12 hs13 hs23
      hc12 hc13 hc23
      hvLoss
      (by simpa [R] using hc1V)
      (by simpa [R] using hc2V)
      (by simpa [R] using hc3V)
      h₁ h₂ h₃
      hmin hs12lt hs23lt

  have hcapR : AngleCap (reindexedPoint p) lam :=
    angleCap_reindexed hcap

  exact fourSupportTwo_derangement_impossible_of_sourceMin_matrix
    (reindexedPoint_injective hp) hcapR
    hn4 hdelta0 hdeltaHalf ht hlam
    hvs1 hvs2 hvs3 hs12 hs13 hs23
    hpat
    hmatrix.2.2.2
    hmatrix.1
    hmatrix.2.1
    hmatrix.2.2.1

theorem planar_threeWholeCube_derangement_sourceGlobalMax_impossible
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
    (hpat :
      FourSupportTwoDerangementPattern9
        (reindexedPoint p) delta lam v s₁ s₂ s₃)
    (hmax :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ w : ProjectionOrdered V, w ≠ v → w < v)
    (hs12lt :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      s₁ < s₂)
    (hs23lt :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      s₂ < s₃) :
    False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam

  have hactive' : retainedActive R v = {c₁,c₂,c₃} := by
    simpa [R] using hactive
  have hc1V : c₁ ∈ retainedActive R v := by
    rw [hactive']
    simp
  have hc2V : c₂ ∈ retainedActive R v := by
    rw [hactive']
    simp
  have hc3V : c₃ ∈ retainedActive R v := by
    rw [hactive']
    simp

  have hmatrix :=
    threeWholeCube_source_globalMax_sameBand_angles
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam Cfam
      hvs1 hvs2 hvs3 hs12 hs13 hs23
      hc12 hc13 hc23
      hvLoss
      (by simpa [R] using hc1V)
      (by simpa [R] using hc2V)
      (by simpa [R] using hc3V)
      h₁ h₂ h₃
      hmax hs12lt hs23lt

  have hcapR : AngleCap (reindexedPoint p) lam :=
    angleCap_reindexed hcap

  exact fourSupportTwo_derangement_impossible_of_sourceMax_matrix
    (reindexedPoint_injective hp) hcapR
    hn4 hdelta0 hdeltaHalf ht hlam
    hvs1 hvs2 hvs3 hs12 hs13 hs23
    hpat
    hmatrix.1
    hmatrix.2.1
    hmatrix.2.2.1
    (by simpa [EuclideanGeometry.angle_comm] using hmatrix.2.2.2)

theorem planar_threeWholeCube_derangement_sourceExtreme_impossible
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
    (hpat :
      FourSupportTwoDerangementPattern9
        (reindexedPoint p) delta lam v s₁ s₂ s₃)
    (hextreme :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      GlobalOrderExtreme v)
    (hs12lt :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      s₁ < s₂)
    (hs23lt :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      s₂ < s₃) :
    False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  rcases hextreme with hmin | hmax
  · exact planar_threeWholeCube_derangement_sourceGlobalMin_impossible
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
      hvs1 hvs2 hvs3 hs12 hs13 hs23
      hc12 hc13 hc23 hactive hvLoss
      h₁ h₂ h₃ hpat hmin hs12lt hs23lt
  · exact planar_threeWholeCube_derangement_sourceGlobalMax_impossible
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
      hvs1 hvs2 hvs3 hs12 hs13 hs23
      hc12 hc13 hc23 hactive hvLoss
      h₁ h₂ h₃ hpat hmax hs12lt hs23lt

#print axioms planar_threeWholeCube_derangement_sourceGlobalMin_impossible
#print axioms planar_threeWholeCube_derangement_sourceGlobalMax_impossible
#print axioms planar_threeWholeCube_derangement_sourceExtreme_impossible

end ProjectionOrdered
end JSP000404Research
