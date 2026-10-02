import JSP000404Research.ProjectionSupportTwoMiddlePairForcing
import JSP000404Research.ProjectionSupportOneConsecutivePalette
import Mathlib.Tactic

/-!
# Ordered geometry in the three-support-two plus one-support-one branch

If four projected-loss second-layer centres share one retained palette and the
left extreme is support-one while the two middle ranks are support-two, then:

* the common retained palette is a consecutive triple, inherited from the
  support-one centre;
* the lower middle support-two centre has its small pair forced to the two
  vertices on its right;
* the upper middle support-two centre has its small pair forced to the two
  vertices on its left.

The right-extreme support-one case is symmetric.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem ordered_commonPalette_leftSupportOne_middleSupportTwo_forcing
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
    {a b c d : ProjectionOrdered V}
    (hab : a < b)
    (hbc : b < c)
    (hcd : c < d)
    (haLoss :
      a ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hbLoss :
      b ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hcLoss :
      c ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (haSecond : centreExponent (Cfam a) t = n - 2)
    (hbSecond : centreExponent (Cfam b) t = n - 2)
    (hcSecond : centreExponent (Cfam c) t = n - 2)
    (haSupport :
      positiveSupport (centreQuotient (Cfam a) t) = 1)
    (hbSupport :
      positiveSupport (centreQuotient (Cfam b) t) = 2)
    (hcSupport :
      positiveSupport (centreQuotient (Cfam c) t) = 2)
    (hpalAB :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R b = retainedActive R a)
    (hpalAC :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R c = retainedActive R a) :
    ∃ m : ℕ,
      (letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
       let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
       (retainedActive R a).map Fin.valEmbedding =
         threeNatInterval m)
      ∧
      EuclideanGeometry.angle
        (reindexedPoint p c)
        (reindexedPoint p b)
        (reindexedPoint p d)
        ≤ delta * lam
      ∧
      EuclideanGeometry.angle
        (reindexedPoint p a)
        (reindexedPoint p c)
        (reindexedPoint p b)
        ≤ delta * lam := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam

  obtain ⟨m,hpalA⟩ :=
    planar_projectedLoss_supportOne_retainedPalette_consecutive
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      Cfam a haLoss haSecond haSupport

  have hpalB :
      (retainedActive R b).map Fin.valEmbedding =
        threeNatInterval m := by
    rw [hpalAB]
    simpa [R,threeNatInterval] using hpalA

  have hpalC :
      (retainedActive R c).map Fin.valEmbedding =
        threeNatInterval m := by
    rw [hpalAC]
    simpa [R,threeNatInterval] using hpalA

  have hbd : b < d := hbc.trans hcd
  have hac : a < c := hab.trans hbc

  have hsmallB :=
    supportTwo_lower_middle_forces_right_pair_small
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam Cfam
      hab hbc hcd hbLoss hbSecond hbSupport
      (by simpa [R,threeNatInterval] using hpalB)

  have hsmallC :=
    supportTwo_upper_middle_forces_left_pair_small
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam Cfam
      hab hbc hcd hcLoss hcSecond hcSupport
      (by simpa [R,threeNatInterval] using hpalC)

  exact ⟨m,
    (by simpa [R,threeNatInterval] using hpalA),
    hsmallB,hsmallC⟩

theorem ordered_commonPalette_rightSupportOne_middleSupportTwo_forcing
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
    {a b c d : ProjectionOrdered V}
    (hab : a < b)
    (hbc : b < c)
    (hcd : c < d)
    (hdLoss :
      d ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hbLoss :
      b ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hcLoss :
      c ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hdSecond : centreExponent (Cfam d) t = n - 2)
    (hbSecond : centreExponent (Cfam b) t = n - 2)
    (hcSecond : centreExponent (Cfam c) t = n - 2)
    (hdSupport :
      positiveSupport (centreQuotient (Cfam d) t) = 1)
    (hbSupport :
      positiveSupport (centreQuotient (Cfam b) t) = 2)
    (hcSupport :
      positiveSupport (centreQuotient (Cfam c) t) = 2)
    (hpalDB :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R b = retainedActive R d)
    (hpalDC :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R c = retainedActive R d) :
    ∃ m : ℕ,
      (letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
       let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
       (retainedActive R d).map Fin.valEmbedding =
         threeNatInterval m)
      ∧
      EuclideanGeometry.angle
        (reindexedPoint p c)
        (reindexedPoint p b)
        (reindexedPoint p d)
        ≤ delta * lam
      ∧
      EuclideanGeometry.angle
        (reindexedPoint p a)
        (reindexedPoint p c)
        (reindexedPoint p b)
        ≤ delta * lam := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam

  obtain ⟨m,hpalD⟩ :=
    planar_projectedLoss_supportOne_retainedPalette_consecutive
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      Cfam d hdLoss hdSecond hdSupport

  have hpalB :
      (retainedActive R b).map Fin.valEmbedding =
        threeNatInterval m := by
    rw [hpalDB]
    simpa [R,threeNatInterval] using hpalD

  have hpalC :
      (retainedActive R c).map Fin.valEmbedding =
        threeNatInterval m := by
    rw [hpalDC]
    simpa [R,threeNatInterval] using hpalD

  have hsmallB :=
    supportTwo_lower_middle_forces_right_pair_small
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam Cfam
      hab hbc hcd hbLoss hbSecond hbSupport
      (by simpa [R,threeNatInterval] using hpalB)

  have hsmallC :=
    supportTwo_upper_middle_forces_left_pair_small
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam Cfam
      hab hbc hcd hcLoss hcSecond hcSupport
      (by simpa [R,threeNatInterval] using hpalC)

  exact ⟨m,
    (by simpa [R,threeNatInterval] using hpalD),
    hsmallB,hsmallC⟩

#print axioms ordered_commonPalette_leftSupportOne_middleSupportTwo_forcing
#print axioms ordered_commonPalette_rightSupportOne_middleSupportTwo_forcing

end ProjectionOrdered
end JSP000404Research
