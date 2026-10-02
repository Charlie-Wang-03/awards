import JSP000404Research.SupportTwoThreeMarkedSmallPair
import JSP000404Research.ProjectionThreeBandOppositeSideGap
import JSP000404Research.ProjectionSupportOneConsecutivePalette
import Mathlib.Tactic

/-!
# Small-pair forcing at the two middle ranks of a four-point order

For a planar projected-loss second-layer support-two centre with a consecutive
three-band retained palette, a delta*lambda-small pair cannot straddle the
centre in generic projection order.

Hence among four ordered points a<i<b<c the support-two small pair at i is
forced to be {b,c}; dually, among a<b<i<c it is forced to be {a,b}.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem supportTwo_lower_middle_forces_right_pair_small
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {a i b c : ProjectionOrdered V}
    (hai : a < i)
    (hib : i < b)
    (hbc : b < c)
    (hiLoss :
      i ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hiSecond :
      centreExponent (Cfam i) t = n - 2)
    (hiSupport :
      positiveSupport (centreQuotient (Cfam i) t) = 2)
    (hpalette :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R i).map Fin.valEmbedding =
        threeNatInterval m) :
    EuclideanGeometry.angle
      (reindexedPoint p b)
      (reindexedPoint p i)
      (reindexedPoint p c)
      ≤ delta * lam := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam
  let exponent := planarCentreExponent hp Cfam

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam Cfam
  have hexp : ∀ q, exponent q ≤ n := by
    intro q
    exact Nat.le_of_lt
      (by simpa [exponent] using hprofile.1 q)
  have hone :
      ∀ q, (active R q).card ≤ n - exponent q + 1 := by
    intro q
    simpa [R,exponent] using hprofile.2 q
  have hiLoss' : i ∈ projectedLossVertices R exponent := by
    simpa [R,exponent] using hiLoss

  have hretA :
      (R.color a i).val < n :=
    projectedLoss_edge_right_retained
      R exponent hexp hone hiLoss' hai
  have hretB :
      (R.color i b).val < n :=
    projectedLoss_edge_right_retained
      R exponent hexp hone hiLoss' hib
  have hic : i < c := lt_trans hib hbc
  have hretC :
      (R.color i c).val < n :=
    projectedLoss_edge_right_retained
      R exponent hexp hone hiLoss' hic

  have hbandA :
      (retainedColor R a i hretA).val ∈ threeNatInterval m := by
    rw [← hpalette]
    exact Finset.mem_map.mpr
      ⟨retainedColor R a i hretA,
       retainedColor_mem_retainedActive_right R hai hretA,rfl⟩
  have hbandB :
      (retainedColor R i b hretB).val ∈ threeNatInterval m := by
    rw [← hpalette]
    exact Finset.mem_map.mpr
      ⟨retainedColor R i b hretB,
       retainedColor_mem_retainedActive_left R hib hretB,rfl⟩
  have hbandC :
      (retainedColor R i c hretC).val ∈ threeNatInterval m := by
    rw [← hpalette]
    exact Finset.mem_map.mpr
      ⟨retainedColor R i c hretC,
       retainedColor_mem_retainedActive_left R hic hretC,rfl⟩

  have hABgt :=
    opposite_side_three_band_angle_gt_delta
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hai hib hretA hretB hbandA hbandB
  have hACgt :=
    opposite_side_three_band_angle_gt_delta
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hai hic hretA hretC hbandA hbandC

  have hsmall :=
    supportTwo_three_other_vertices_has_small_pair
      (reindexedPoint_injective hp)
      hcap hn3 hdelta0 hdeltaHalf ht hlam
      (i := i) (a := a) (b := b) (c := c)
      (ne_of_lt hai).symm
      (ne_of_lt hib)
      (ne_of_lt hic)
      (ne_of_lt (lt_trans hai hib))
      (ne_of_lt (lt_trans (lt_trans hai hib) hbc))
      (ne_of_lt hbc)
      (Cfam i) hiSecond hiSupport

  rcases hsmall with hAB | hBC | hCA
  · exact False.elim ((not_le_of_gt hABgt) hAB)
  · exact hBC
  · have hAC :
        EuclideanGeometry.angle
          (reindexedPoint p a)
          (reindexedPoint p i)
          (reindexedPoint p c)
          ≤ delta * lam := by
      simpa [EuclideanGeometry.angle_comm] using hCA
    exact False.elim ((not_le_of_gt hACgt) hAC)

theorem supportTwo_upper_middle_forces_left_pair_small
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {a b i c : ProjectionOrdered V}
    (hab : a < b)
    (hbi : b < i)
    (hic : i < c)
    (hiLoss :
      i ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hiSecond :
      centreExponent (Cfam i) t = n - 2)
    (hiSupport :
      positiveSupport (centreQuotient (Cfam i) t) = 2)
    (hpalette :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R i).map Fin.valEmbedding =
        threeNatInterval m) :
    EuclideanGeometry.angle
      (reindexedPoint p a)
      (reindexedPoint p i)
      (reindexedPoint p b)
      ≤ delta * lam := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam
  let exponent := planarCentreExponent hp Cfam

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam Cfam
  have hexp : ∀ q, exponent q ≤ n := by
    intro q
    exact Nat.le_of_lt
      (by simpa [exponent] using hprofile.1 q)
  have hone :
      ∀ q, (active R q).card ≤ n - exponent q + 1 := by
    intro q
    simpa [R,exponent] using hprofile.2 q
  have hiLoss' : i ∈ projectedLossVertices R exponent := by
    simpa [R,exponent] using hiLoss

  have hai : a < i := lt_trans hab hbi
  have hretA :
      (R.color a i).val < n :=
    projectedLoss_edge_right_retained
      R exponent hexp hone hiLoss' hai
  have hretB :
      (R.color b i).val < n :=
    projectedLoss_edge_right_retained
      R exponent hexp hone hiLoss' hbi
  have hretC :
      (R.color i c).val < n :=
    projectedLoss_edge_right_retained
      R exponent hexp hone hiLoss' hic

  have hbandA :
      (retainedColor R a i hretA).val ∈ threeNatInterval m := by
    rw [← hpalette]
    exact Finset.mem_map.mpr
      ⟨retainedColor R a i hretA,
       retainedColor_mem_retainedActive_right R hai hretA,rfl⟩
  have hbandB :
      (retainedColor R b i hretB).val ∈ threeNatInterval m := by
    rw [← hpalette]
    exact Finset.mem_map.mpr
      ⟨retainedColor R b i hretB,
       retainedColor_mem_retainedActive_right R hbi hretB,rfl⟩
  have hbandC :
      (retainedColor R i c hretC).val ∈ threeNatInterval m := by
    rw [← hpalette]
    exact Finset.mem_map.mpr
      ⟨retainedColor R i c hretC,
       retainedColor_mem_retainedActive_left R hic hretC,rfl⟩

  have hBCgt :=
    opposite_side_three_band_angle_gt_delta
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hbi hic hretB hretC hbandB hbandC
  have hACgt :=
    opposite_side_three_band_angle_gt_delta
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hai hic hretA hretC hbandA hbandC

  have hsmall :=
    supportTwo_three_other_vertices_has_small_pair
      (reindexedPoint_injective hp)
      hcap hn3 hdelta0 hdeltaHalf ht hlam
      (i := i) (a := a) (b := b) (c := c)
      (ne_of_lt hai).symm
      (ne_of_lt hbi).symm
      (ne_of_lt hic)
      (ne_of_lt hab)
      (ne_of_lt (lt_trans (lt_trans hab hbi) hic))
      (ne_of_lt (lt_trans hbi hic))
      (Cfam i) hiSecond hiSupport

  rcases hsmall with hAB | hBC | hCA
  · exact hAB
  · have hBC' :
        EuclideanGeometry.angle
          (reindexedPoint p b)
          (reindexedPoint p i)
          (reindexedPoint p c)
          ≤ delta * lam := hBC
    exact False.elim ((not_le_of_gt hBCgt) hBC')
  · have hAC :
        EuclideanGeometry.angle
          (reindexedPoint p a)
          (reindexedPoint p i)
          (reindexedPoint p c)
          ≤ delta * lam := by
      simpa [EuclideanGeometry.angle_comm] using hCA
    exact False.elim ((not_le_of_gt hACgt) hAC)

#print axioms supportTwo_lower_middle_forces_right_pair_small
#print axioms supportTwo_upper_middle_forces_left_pair_small

end ProjectionOrdered
end JSP000404Research
