import JSP000404Research.StandardResidualRetainedBandBounds
import JSP000404Research.PlanarStandardResidualColoring
import Mathlib.Tactic

/-!
# Same-side small angle forces retained band labels one step close

For two retained edges on the same side of a centre in generic projection
order, the actual angle is the absolute difference of the corresponding
forward lifted directions.  Under the standard residual colouring, an edge
of retained colour c has normalized direction in [c,c+1).

Hence an angle at most delta*lambda with delta<1/2 cannot occur between bands
whose labels differ by two or more.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem right_same_side_small_angle_labels_one_step_close
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn1 : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i j k : ProjectionOrdered V}
    (hij :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      i < j)
    (hjk :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      j < k)
    (hretJ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      (R.color i j).val < n)
    (hretK :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      (R.color i k).val < n)
    (hsmall :
      EuclideanGeometry.angle
        (reindexedPoint p j)
        (reindexedPoint p i)
        (reindexedPoint p k)
        ≤ delta * lam) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let R :=
      planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
    let cj := retainedColor R i j hretJ
    let ck := retainedColor R i k hretK
    cj.val ≤ ck.val + 1 ∧ ck.val ≤ cj.val + 1 := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hdelta1 : delta < 1 := by linarith
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

  let F := genericForwardAngleLift hp
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let R := standardResidualColoring D n hwidth

  have hretJ' : (R.color i j).val < n := by
    simpa [R,D,planarStandardResidualColoring] using hretJ
  have hik : i < k := hij.trans hjk
  have hretK' : (R.color i k).val < n := by
    simpa [R,D,planarStandardResidualColoring] using hretK
  let cj : Fin n := retainedColor R i j hretJ'
  let ck : Fin n := retainedColor R i k hretK'

  have hJ :=
    standardResidual_retained_edge_exact_band_bounds
      D hwidth hij hretJ'
  have hK :=
    standardResidual_retained_edge_exact_band_bounds
      D hwidth hik hretK'

  have hang :=
    F.angle_first_eq_abs hij hjk
  have habs :=
    F.abs_value_sub_value hlampos i j i k
  have hFD :
      D.value i j = F.value (lam := lam) i j ∧
      D.value i k = F.value (lam := lam) i k := by
    exact ⟨rfl,rfl⟩

  have hdiff :
      |D.value i j - D.value i k| ≤ delta := by
    have hangle :
        |F.theta i j - F.theta i k| ≤ delta * lam := by
      rw [← hang]
      simpa [F,reindexedPoint] using hsmall
    have hdiv :
        |F.theta i j - F.theta i k| / lam ≤ delta := by
      exact (div_le_iff₀ hlampos).2 (by
        simpa [mul_comm] using hangle)
    rw [← habs] at hdiv
    rw [hFD.1, hFD.2]
    exact hdiv

  have hCJlo : (cj.val : ℝ) ≤ D.value i j := by
    simpa [cj] using hJ.1
  have hCJhi : D.value i j < (cj.val : ℝ) + 1 := by
    simpa [cj] using hJ.2
  have hCKlo : (ck.val : ℝ) ≤ D.value i k := by
    simpa [ck] using hK.1
  have hCKhi : D.value i k < (ck.val : ℝ) + 1 := by
    simpa [ck] using hK.2

  have hcloseR :
      ((cj.val : ℝ) < (ck.val : ℝ) + 2) ∧
      ((ck.val : ℝ) < (cj.val : ℝ) + 2) := by
    rw [abs_le] at hdiff
    constructor <;> linarith

  have hCJnat : cj.val < ck.val + 2 := by
    exact_mod_cast hcloseR.1
  have hCKnat : ck.val < cj.val + 2 := by
    exact_mod_cast hcloseR.2
  have hcloseN :
      cj.val ≤ ck.val + 1 ∧ ck.val ≤ cj.val + 1 := by
    omega

  simpa [R,D,cj,ck,planarStandardResidualColoring] using hcloseN

theorem left_same_side_small_angle_labels_one_step_close
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn1 : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i j k : ProjectionOrdered V}
    (hjk :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      j < k)
    (hki :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      k < i)
    (hretJ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      (R.color j i).val < n)
    (hretK :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
      (R.color k i).val < n)
    (hsmall :
      EuclideanGeometry.angle
        (reindexedPoint p j)
        (reindexedPoint p i)
        (reindexedPoint p k)
        ≤ delta * lam) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let R :=
      planarStandardResidualColoring
        hp hcap hn1 hdelta0 (by linarith : delta < 1) ht hlam
    let cj := retainedColor R j i hretJ
    let ck := retainedColor R k i hretK
    cj.val ≤ ck.val + 1 ∧ ck.val ≤ cj.val + 1 := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hdelta1 : delta < 1 := by linarith
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

  let F := genericForwardAngleLift hp
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let R := standardResidualColoring D n hwidth

  have hji : j < i := hjk.trans hki
  have hretJ' : (R.color j i).val < n := by
    simpa [R,D,planarStandardResidualColoring] using hretJ
  have hretK' : (R.color k i).val < n := by
    simpa [R,D,planarStandardResidualColoring] using hretK
  let cj : Fin n := retainedColor R j i hretJ'
  let ck : Fin n := retainedColor R k i hretK'

  have hJ :=
    standardResidual_retained_edge_exact_band_bounds
      D hwidth hji hretJ'
  have hK :=
    standardResidual_retained_edge_exact_band_bounds
      D hwidth hki hretK'

  have hang :=
    F.angle_last_eq_abs hjk hki
  have habs :=
    F.abs_value_sub_value hlampos j i k i
  have hFD :
      D.value j i = F.value (lam := lam) j i ∧
      D.value k i = F.value (lam := lam) k i := by
    exact ⟨rfl,rfl⟩

  have hdiff :
      |D.value j i - D.value k i| ≤ delta := by
    have hangle :
        |F.theta j i - F.theta k i| ≤ delta * lam := by
      rw [← hang]
      simpa [F,reindexedPoint] using hsmall
    have hdiv :
        |F.theta j i - F.theta k i| / lam ≤ delta := by
      exact (div_le_iff₀ hlampos).2 (by
        simpa [mul_comm] using hangle)
    rw [← habs] at hdiv
    rw [hFD.1, hFD.2]
    exact hdiv

  have hCJlo : (cj.val : ℝ) ≤ D.value j i := by
    simpa [cj] using hJ.1
  have hCJhi : D.value j i < (cj.val : ℝ) + 1 := by
    simpa [cj] using hJ.2
  have hCKlo : (ck.val : ℝ) ≤ D.value k i := by
    simpa [ck] using hK.1
  have hCKhi : D.value k i < (ck.val : ℝ) + 1 := by
    simpa [ck] using hK.2

  have hcloseR :
      ((cj.val : ℝ) < (ck.val : ℝ) + 2) ∧
      ((ck.val : ℝ) < (cj.val : ℝ) + 2) := by
    rw [abs_le] at hdiff
    constructor <;> linarith

  have hCJnat : cj.val < ck.val + 2 := by
    exact_mod_cast hcloseR.1
  have hCKnat : ck.val < cj.val + 2 := by
    exact_mod_cast hcloseR.2
  have hcloseN :
      cj.val ≤ ck.val + 1 ∧ ck.val ≤ cj.val + 1 := by
    omega

  simpa [R,D,cj,ck,planarStandardResidualColoring] using hcloseN

#print axioms right_same_side_small_angle_labels_one_step_close
#print axioms left_same_side_small_angle_labels_one_step_close

end ProjectionOrdered
end JSP000404Research
