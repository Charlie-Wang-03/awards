import JSP000404Research.FourCycleBandCloseness
import JSP000404Research.PlanarStandardResidualColoring
import Mathlib.Tactic

/-!
# Opposite-side retained rays cannot be delta-small

In the standard lower-branch residual colouring, every retained edge lies in
one of the first n unit bands.  Hence every retained normalized forward
direction lies in [0,n), independently of which retained colour it uses.

For a<i<b the actual angle at i is the supplement of the difference of the two
forward lifted directions.  Since that normalized difference is strictly less
than n and pi=(n+delta)lambda, the angle is strictly larger than delta*lambda.

This removes the earlier unnecessary three-consecutive-palette hypothesis from
the opposite-side small-angle obstruction.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem opposite_side_retained_angle_gt_delta
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn1 : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a i b : ProjectionOrdered V}
    (hai :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      a < i)
    (hib :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      i < b)
    (hretA :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn1 hdelta0 hdelta1 ht hlam
      (R.color a i).val < n)
    (hretB :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn1 hdelta0 hdelta1 ht hlam
      (R.color i b).val < n) :
    delta * lam <
      EuclideanGeometry.angle
        (reindexedPoint p a)
        (reindexedPoint p i)
        (reindexedPoint p b) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (1 : ℝ) ≤ n := by
      exact_mod_cast hn1
    linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos

  have hwidthR : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hwidth : t < (n + 1 : ℕ) := by
    exact_mod_cast hwidthR

  let D := genericDirectionData_sendov hp hcap htpos hlam
  let R : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    DirectionData.standardResidualColoring D n hwidth
  let F := genericForwardAngleLift hp

  have hretA' : (R.color a i).val < n := by
    simpa [R, D, planarStandardResidualColoring] using hretA
  have hretB' : (R.color i b).val < n := by
    simpa [R, D, planarStandardResidualColoring] using hretB

  let cA : Fin n := retainedColor R a i hretA'
  let cB : Fin n := retainedColor R i b hretB'

  have hfullA : R.color a i = cA.castSucc := by
    apply Fin.ext
    rfl
  have hfullB : R.color i b = cB.castSucc := by
    apply Fin.ext
    rfl

  have hfullA' :
      DirectionData.standardBandColor
          D (n + 1) (Nat.succ_pos n)
          (by exact_mod_cast hwidth) a i
        = cA.castSucc := by
    simpa [R, DirectionData.standardResidualColoring,
      DirectionData.standardBandColoring] using hfullA
  have hfullB' :
      DirectionData.standardBandColor
          D (n + 1) (Nat.succ_pos n)
          (by exact_mod_cast hwidth) i b
        = cB.castSucc := by
    simpa [R, DirectionData.standardResidualColoring,
      DirectionData.standardBandColoring] using hfullB

  have hAraw :=
    (DirectionData.standardBandColor_eq_iff
      D (n + 1) (Nat.succ_pos n)
      (by exact_mod_cast hwidth)
      hai cA.castSucc).1 hfullA'
  have hBraw :=
    (DirectionData.standardBandColor_eq_iff
      D (n + 1) (Nat.succ_pos n)
      (by exact_mod_cast hwidth)
      hib cB.castSucc).1 hfullB'

  have hAval :
      (cA.val : ℝ) ≤ D.value a i ∧
      D.value a i < (cA.val : ℝ) + 1 := by
    simpa using hAraw
  have hBval :
      (cB.val : ℝ) ≤ D.value i b ∧
      D.value i b < (cB.val : ℝ) + 1 := by
    simpa using hBraw

  have hcAhi : cA.val + 1 ≤ n := Nat.succ_le_iff.mpr cA.isLt
  have hcBhi : cB.val + 1 ≤ n := Nat.succ_le_iff.mpr cB.isLt
  have hA0 : 0 ≤ D.value a i := by
    have hc0 : (0 : ℝ) ≤ cA.val := by positivity
    linarith
  have hB0 : 0 ≤ D.value i b := by
    have hc0 : (0 : ℝ) ≤ cB.val := by positivity
    linarith
  have hAn : D.value a i < (n : ℝ) := by
    have hc : (cA.val : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast hcAhi
    linarith
  have hBn : D.value i b < (n : ℝ) := by
    have hc : (cB.val : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast hcBhi
    linarith

  have hdiffVal :
      |D.value a i - D.value i b| < (n : ℝ) := by
    rw [abs_lt]
    constructor <;> linarith

  have hvalA :
      F.value (lam := lam) a i = D.value a i := by
    unfold ForwardAngleLift.value
    rw [genericDirectionData_sendov_value hp hcap htpos hlam a i]
    rfl
  have hvalB :
      F.value (lam := lam) i b = D.value i b := by
    unfold ForwardAngleLift.value
    rw [genericDirectionData_sendov_value hp hcap htpos hlam i b]
    rfl
  have habs :=
    F.abs_value_sub_value hlampos a i i b
  rw [hvalA, hvalB] at habs
  have hdiffTheta :
      |F.theta a i - F.theta i b| / lam < (n : ℝ) := by
    rw [← habs]
    exact hdiffVal
  have htheta :
      |F.theta a i - F.theta i b| < (n : ℝ) * lam := by
    exact (div_lt_iff₀ hlampos).mp hdiffTheta

  have hang := F.angle_middle_eq_pi_sub_abs hai hib
  have hpi : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  rw [hang, hpi, ht]
  nlinarith

theorem opposite_side_retained_not_delta_small
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn1 : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a i b : ProjectionOrdered V}
    (hai :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      a < i)
    (hib :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      i < b)
    (hretA :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn1 hdelta0 hdelta1 ht hlam
      (R.color a i).val < n)
    (hretB :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn1 hdelta0 hdelta1 ht hlam
      (R.color i b).val < n)
    (hsmall :
      EuclideanGeometry.angle
        (reindexedPoint p a)
        (reindexedPoint p i)
        (reindexedPoint p b) ≤ delta * lam) :
    False := by
  have hgt :=
    opposite_side_retained_angle_gt_delta
      hp hcap hn1 hdelta0 hdelta1 ht hlam
      hai hib hretA hretB
  linarith

#print axioms opposite_side_retained_angle_gt_delta
#print axioms opposite_side_retained_not_delta_small


/-- If the two retained colours on opposite sides of the centre are at most
one band apart, then the actual angle is larger than pi - 2*lambda. -/
theorem opposite_side_oneStep_retained_angle_gt_pi_sub_two_lam
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn1 : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a i b : ProjectionOrdered V}
    (hai :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      a < i)
    (hib :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      i < b)
    (hretA :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn1 hdelta0 hdelta1 ht hlam
      (R.color a i).val < n)
    (hretB :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn1 hdelta0 hdelta1 ht hlam
      (R.color i b).val < n)
    (hclose :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn1 hdelta0 hdelta1 ht hlam
      let cA := retainedColor R a i hretA
      let cB := retainedColor R i b hretB
      NatOneStepClose cA.val cB.val) :
    Real.pi - 2 * lam <
      EuclideanGeometry.angle
        (reindexedPoint p a)
        (reindexedPoint p i)
        (reindexedPoint p b) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hwidthR : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hwidth : t < (n + 1 : ℕ) := by
    exact_mod_cast hwidthR

  let D := genericDirectionData_sendov hp hcap htpos hlam
  let R : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    DirectionData.standardResidualColoring D n hwidth
  let F := genericForwardAngleLift hp

  have hretA' : (R.color a i).val < n := by
    simpa [R, D, planarStandardResidualColoring] using hretA
  have hretB' : (R.color i b).val < n := by
    simpa [R, D, planarStandardResidualColoring] using hretB

  let cA : Fin n := retainedColor R a i hretA'
  let cB : Fin n := retainedColor R i b hretB'

  have hclose' : NatOneStepClose cA.val cB.val := by
    simpa [R, D, cA, cB, planarStandardResidualColoring] using hclose

  have hA :=
    DirectionData.standardResidual_retained_edge_exact_band_bounds
      D hwidth hai hretA'
  have hB :=
    DirectionData.standardResidual_retained_edge_exact_band_bounds
      D hwidth hib hretB'

  have hlabel :
      |(cA.val : ℝ) - (cB.val : ℝ)| ≤ 1 := by
    unfold NatOneStepClose at hclose'
    rw [abs_le]
    constructor <;> exact_mod_cast (show
      cA.val ≤ cB.val + 1 ∧ cB.val ≤ cA.val + 1 from hclose') <;>
      omega

  have hdiffVal :
      |D.value a i - D.value i b| < 2 := by
    rw [abs_lt]
    unfold NatOneStepClose at hclose'
    constructor <;> nlinarith [hA.1,hA.2,hB.1,hB.2,
      (show (cA.val : ℝ) ≤ (cB.val : ℝ) + 1 by exact_mod_cast hclose'.1),
      (show (cB.val : ℝ) ≤ (cA.val : ℝ) + 1 by exact_mod_cast hclose'.2)]

  have hvalA : F.value (lam := lam) a i = D.value a i := by
    unfold ForwardAngleLift.value
    rw [genericDirectionData_sendov_value hp hcap htpos hlam a i]
    rfl
  have hvalB : F.value (lam := lam) i b = D.value i b := by
    unfold ForwardAngleLift.value
    rw [genericDirectionData_sendov_value hp hcap htpos hlam i b]
    rfl

  have habs := F.abs_value_sub_value hlampos a i i b
  rw [hvalA, hvalB] at habs
  have hdiv :
      |F.theta a i - F.theta i b| / lam < 2 := by
    rw [← habs]
    exact hdiffVal
  have htheta :
      |F.theta a i - F.theta i b| < 2 * lam := by
    exact (div_lt_iff₀ hlampos).mp
      (by simpa [mul_comm] using hdiv)

  have hang := F.angle_middle_eq_pi_sub_abs hai hib
  rw [hang]
  linarith

#print axioms opposite_side_oneStep_retained_angle_gt_pi_sub_two_lam

end ProjectionOrdered
end JSP000404Research
