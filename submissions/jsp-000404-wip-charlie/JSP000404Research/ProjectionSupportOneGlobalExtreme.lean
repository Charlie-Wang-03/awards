import JSP000404Research.ProjectionThreeBandOppositeSideGap
import JSP000404Research.ProjectionSupportOneConsecutivePalette
import JSP000404Research.SupportOneNarrowCone
import Mathlib.Tactic

/-!
# Planar second-layer support-one centres are order extremes for n >= 4

A projected-loss second-layer support-one centre has a consecutive retained
palette {m,m+1,m+2} and all angles between rays from the centre are at most
(1+delta)*lambda.

If it had one vertex on each side in the generic projection order, the two
incident retained edge directions would both lie in the same three-band
window.  Their normalized forward-direction difference is therefore < 3, so
the middle angle is > pi-3*lambda.

For n>=4,

  pi - 3*lambda
    = (n+delta-3)*lambda
    >= (1+delta)*lambda,

contradicting the support-one narrow-cone bound.

Hence every such centre is a global minimum or global maximum of the generic
projection order.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

def GlobalOrderExtreme
    {V : Type*} [LinearOrder V]
    (i : V) : Prop :=
  (∀ w : V, w ≠ i → i < w) ∨
  (∀ w : V, w ≠ i → w < i)

theorem planar_projectedLoss_secondLayer_supportOne_globalExtreme
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
    (C :
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    (i : ProjectionOrdered V)
    (hloss :
      i ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hsecond :
      centreExponent (C i) t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient (C i) t) = 1)
    (H :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t i (C i)) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    GlobalOrderExtreme i := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn3 : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  have htpos : 0 < t :=
    sendov_scale_pos hn1 hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hwidthR : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hwidth : t < (n + 1 : ℕ) := by
    exact_mod_cast hwidthR

  let F := genericForwardAngleLift hp
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let R := standardResidualColoring D n hwidth
  let exponent := planarCentreExponent hp C

  have hloss' : i ∈ projectedLossVertices R exponent := by
    simpa [R,D,exponent,planarStandardResidualColoring,
      planarCentreExponent] using hloss

  obtain ⟨m,hpalette⟩ :=
    planar_projectedLoss_supportOne_retainedPalette_consecutive
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      C i hloss hsecond hsupport
  have hpalette' :
      (retainedActive R i).map Fin.valEmbedding =
        threeNatInterval m := by
    simpa [R,D,threeNatInterval] using hpalette

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap hn1 hdelta0 hdelta1 ht hlam C
  have hexp : ∀ q, exponent q ≤ n := by
    intro q
    exact Nat.le_of_lt
      (by simpa [exponent] using hprofile.1 q)
  have hone :
      ∀ q, (active R q).card ≤ n - exponent q + 1 := by
    intro q
    simpa [R,D,exponent] using hprofile.2 q

  by_cases hleft : ∃ a : ProjectionOrdered V, a < i
  · obtain ⟨a,hai⟩ := hleft
    by_cases hright : ∃ b : ProjectionOrdered V, i < b
    · obtain ⟨b,hib⟩ := hright

      have hretA :
          (R.color a i).val < n :=
        projectedLoss_edge_right_retained
          R exponent hexp hone hloss' hai
      have hretB :
          (R.color i b).val < n :=
        projectedLoss_edge_right_retained
          R exponent hexp hone hloss' hib

      let ca : Fin n := retainedColor R a i hretA
      let cb : Fin n := retainedColor R i b hretB
      have hcaI : ca ∈ retainedActive R i :=
        retainedColor_mem_retainedActive_right R hai hretA
      have hcbI : cb ∈ retainedActive R i :=
        retainedColor_mem_retainedActive_left R hib hretB
      have hcaBand : ca.val ∈ threeNatInterval m := by
        rw [← hpalette']
        exact Finset.mem_map.mpr ⟨ca,hcaI,rfl⟩
      have hcbBand : cb.val ∈ threeNatInterval m := by
        rw [← hpalette']
        exact Finset.mem_map.mpr ⟨cb,hcbI,rfl⟩

      have hA :=
        standardResidual_retained_edge_exact_band_bounds
          D hwidth hai hretA
      have hB :=
        standardResidual_retained_edge_exact_band_bounds
          D hwidth hib hretB
      have hcA := mem_threeNatInterval_iff_bounds.mp hcaBand
      have hcB := mem_threeNatInterval_iff_bounds.mp hcbBand
      have hcAlo : (m : ℝ) ≤ (ca.val : ℝ) := by
        exact_mod_cast hcA.1
      have hcAhi : (ca.val : ℝ) ≤ (m : ℝ) + 2 := by
        exact_mod_cast hcA.2
      have hcBlo : (m : ℝ) ≤ (cb.val : ℝ) := by
        exact_mod_cast hcB.1
      have hcBhi : (cb.val : ℝ) ≤ (m : ℝ) + 2 := by
        exact_mod_cast hcB.2
      have hAval :
          (m : ℝ) ≤ D.value a i ∧
          D.value a i < (m : ℝ) + 3 := by
        constructor
        · exact hcAlo.trans hA.1
        · linarith [hA.2,hcAhi]
      have hBval :
          (m : ℝ) ≤ D.value i b ∧
          D.value i b < (m : ℝ) + 3 := by
        constructor
        · exact hcBlo.trans hB.1
        · linarith [hB.2,hcBhi]
      have hdiff :
          |D.value a i - D.value i b| < 3 := by
        rw [abs_lt]
        constructor <;>
          linarith [hAval.1,hAval.2,hBval.1,hBval.2]

      have hFD :
          ∀ x y : ProjectionOrdered V,
            D.value x y = F.value (lam := lam) x y := by
        intro x y
        rfl
      have habs := F.abs_value_sub_value hlampos a i i b
      rw [← hFD a i, ← hFD i b] at habs
      have htheta :
          |F.theta a i - F.theta i b| < 3 * lam := by
        have hdiv :
            |F.theta a i - F.theta i b| / lam < 3 := by
          rw [← habs]
          exact hdiff
        exact (div_lt_iff₀ hlampos).mp
          (by simpa [mul_comm] using hdiv)

      have hangEq := F.angle_middle_eq_pi_sub_abs hai hib
      have hlower :
          Real.pi - 3 * lam <
            EuclideanGeometry.angle
              (reindexedPoint p a)
              (reindexedPoint p i)
              (reindexedPoint p b) := by
        rw [hangEq]
        linarith

      have hupper :=
        secondLayer_supportOne_all_angles_le_one_add_delta_lam
          (reindexedPoint_injective hp)
          hn3 hdelta0 ht hlam
          (C i) hsecond hsupport H
          (ne_of_lt hai) (ne_of_gt hib)

      have hpi : Real.pi = t * lam := by
        rw [hlam]
        field_simp [ne_of_gt htpos]
      have hthreshold :
          (1 + delta) * lam ≤ Real.pi - 3 * lam := by
        rw [hpi,ht]
        have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
        nlinarith
      exfalso
      exact (not_lt_of_ge (hupper.trans hthreshold)) hlower
    · left
      intro w hwi
      rcases lt_or_gt_of_ne hwi with hwiLt | hiw
      · exact False.elim (hright ⟨w,hwiLt⟩)
      · exact hiw
  · right
    intro w hwi
    rcases lt_or_gt_of_ne hwi with hwiLt | hiw
    · exact hwiLt
    · exact False.elim (hleft ⟨w,hiw⟩)

#print axioms planar_projectedLoss_secondLayer_supportOne_globalExtreme

end ProjectionOrdered
end JSP000404Research
