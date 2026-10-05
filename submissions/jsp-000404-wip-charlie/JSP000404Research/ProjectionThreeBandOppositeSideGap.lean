import JSP000404Research.ProjectionFiveBandDirectionWindow
import JSP000404Research.ProjectionSupportOneConsecutivePalette
import JSP000404Research.StandardResidualRetainedBandBounds
import JSP000404Research.PlanarDirectionBridge
import Mathlib.Tactic

/-!
# Opposite-side rays cannot form a delta-small pair inside three bands

For the generic-projection residual colouring, a retained edge of colour c has
normalized forward direction in [c,c+1).

If two edges incident to a centre have colours in one three-consecutive palette
{m,m+1,m+2}, both forward direction values lie in [m,m+3), hence differ by
strictly less than 3.

When the two endpoints lie on opposite sides of the centre in projection order,
the actual angle at the centre is the supplement of that forward-direction
difference.  Therefore

  angle > pi - 3*lambda
        = (n+delta-3)*lambda
        >= delta*lambda

for n>=3.

Thus no delta*lambda-small pair can straddle the centre.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem opposite_side_three_band_angle_gt_delta
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
    {a i b : ProjectionOrdered V}
    (hai : a < i)
    (hib : i < b)
    (hretA :
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (R.color a i).val < n)
    (hretB :
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (R.color i b).val < n)
    (hbandA :
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedColor R a i hretA).val ∈ threeNatInterval m)
    (hbandB :
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedColor R i b hretB).val ∈ threeNatInterval m) :
    delta * lam <
      EuclideanGeometry.angle
        (reindexedPoint p a)
        (reindexedPoint p i)
        (reindexedPoint p b) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
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

  let F :=
    genericForwardAngleLift hp
  let D :=
    genericDirectionData_sendov hp hcap htpos hlam
  let R :=
    standardResidualColoring D n hwidth

  have hretA' : (R.color a i).val < n := by
    simpa [R,D,planarStandardResidualColoring] using hretA
  have hretB' : (R.color i b).val < n := by
    simpa [R,D,planarStandardResidualColoring] using hretB
  have hbandA' :
      (retainedColor R a i hretA').val ∈ threeNatInterval m := by
    simpa [R,D,planarStandardResidualColoring] using hbandA
  have hbandB' :
      (retainedColor R i b hretB').val ∈ threeNatInterval m := by
    simpa [R,D,planarStandardResidualColoring] using hbandB

  have hA :=
    standardResidual_retained_edge_exact_band_bounds
      D hwidth hai hretA'
  have hB :=
    standardResidual_retained_edge_exact_band_bounds
      D hwidth hib hretB'

  have hcA :=
    mem_threeNatInterval_iff_bounds.mp hbandA'
  have hcB :=
    mem_threeNatInterval_iff_bounds.mp hbandB'

  have hcAlo :
      (m : ℝ) ≤
        ((retainedColor R a i hretA').val : ℝ) := by
    exact_mod_cast hcA.1
  have hcAhi :
      ((retainedColor R a i hretA').val : ℝ)
        ≤ (m : ℝ) + 2 := by
    exact_mod_cast hcA.2
  have hcBlo :
      (m : ℝ) ≤
        ((retainedColor R i b hretB').val : ℝ) := by
    exact_mod_cast hcB.1
  have hcBhi :
      ((retainedColor R i b hretB').val : ℝ)
        ≤ (m : ℝ) + 2 := by
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

  have hdiffVal :
      |D.value a i - D.value i b| < 3 := by
    rw [abs_lt]
    constructor <;> linarith [hAval.1,hAval.2,hBval.1,hBval.2]

  have hFD :
      ∀ x y : ProjectionOrdered V,
        D.value x y =
          F.value (lam := lam) x y := by
    intro x y
    rfl

  have habs :=
    F.abs_value_sub_value hlampos a i i b
  rw [← hFD a i, ← hFD i b] at habs
  have hdiv :
      |F.theta a i - F.theta i b| / lam < 3 := by
    rw [← habs]
    exact hdiffVal
  have htheta :
      |F.theta a i - F.theta i b| < 3 * lam := by
    exact (div_lt_iff₀ hlampos).mp
      (by simpa [mul_comm] using hdiv)

  have hang :=
    F.angle_middle_eq_pi_sub_abs hai hib
  have hpi : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  rw [hang,hpi,ht]
  have hnR : (3 : ℝ) ≤ n := by
    exact_mod_cast hn3
  nlinarith

#print axioms opposite_side_three_band_angle_gt_delta

end ProjectionOrdered
end JSP000404Research
