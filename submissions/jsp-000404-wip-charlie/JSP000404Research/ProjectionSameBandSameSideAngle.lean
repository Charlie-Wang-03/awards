import JSP000404Research.GenericForwardAngleLift
import JSP000404Research.StandardResidual
import Mathlib.Tactic

/-!
# Same standard band on one side gives an angle below lambda

For the generic-projection DirectionData, two increasing edges in the same
standard unit band have normalized direction values differing by less than one.
The ForwardAngleLift formulas identify the angle at a common first endpoint,
or a common last endpoint, with the absolute difference of the lifted forward
directions.  Hence two same-colour neighbours lying on the same side of a
centre subtend angle < lambda.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem same_standardBand_common_first_angle_lt_lam
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i x y : ProjectionOrdered V}
    (hix : i < x)
    (hiy : i < y)
    (hxy : x ≠ y)
    (heq :
      let D :=
        genericDirectionData_sendov hp hcap
          (sendov_scale_pos hn hdelta0 ht) hlam
      let R :=
        DirectionData.standardResidualColoring D n
          (by rw [ht]; push_cast; linarith)
      R.color i x = R.color i y) :
    EuclideanGeometry.angle
        (reindexedPoint p x) (reindexedPoint p i) (reindexedPoint p y)
      < lam := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htpos := sendov_scale_pos hn hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hwidth : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let R := DirectionData.standardResidualColoring D n hwidth
  let F := genericForwardAngleLift hp

  have heq' : R.color i x = R.color i y := by
    simpa [D,R] using heq
  let c : Fin (n+1) := R.color i x
  have hxBand :
      ((c : Fin (n+1)) : ℝ) ≤ D.value i x ∧
      D.value i x < ((c : Fin (n+1)) : ℝ) + 1 := by
    apply
      (DirectionData.standardBandColor_eq_iff
        D (n+1) (Nat.succ_pos n)
        (by exact_mod_cast hwidth)
        hix c).1
    rfl
  have hyBand :
      ((c : Fin (n+1)) : ℝ) ≤ D.value i y ∧
      D.value i y < ((c : Fin (n+1)) : ℝ) + 1 := by
    apply
      (DirectionData.standardBandColor_eq_iff
        D (n+1) (Nat.succ_pos n)
        (by exact_mod_cast hwidth)
        hiy c).1
    simpa [c] using heq'.symm
  have hval :
      |D.value i x - D.value i y| < 1 := by
    rw [abs_lt]
    constructor <;> linarith

  have htheta :
      |projectionLiftedAngle (genericProjectionSlope p)
          (p x.toOriginal - p i.toOriginal) -
        projectionLiftedAngle (genericProjectionSlope p)
          (p y.toOriginal - p i.toOriginal)| < lam := by
    rw [genericDirectionData_sendov_value
          hp hcap htpos hlam i x,
        genericDirectionData_sendov_value
          hp hcap htpos hlam i y] at hval
    have hre :
        ((projectionLiftedAngle (genericProjectionSlope p)
            (p x.toOriginal - p i.toOriginal) -
          projectionAngleBase (genericProjectionSlope p)) / lam) -
        ((projectionLiftedAngle (genericProjectionSlope p)
            (p y.toOriginal - p i.toOriginal) -
          projectionAngleBase (genericProjectionSlope p)) / lam)
        =
        (projectionLiftedAngle (genericProjectionSlope p)
            (p x.toOriginal - p i.toOriginal) -
         projectionLiftedAngle (genericProjectionSlope p)
            (p y.toOriginal - p i.toOriginal)) / lam := by
      ring
    rw [hre, abs_div, abs_of_pos hlampos] at hval
    exact (div_lt_one hlampos).mp hval

  rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
  · have hang :=
      F.angle_first_eq_abs hix hxylt
    simpa [F,genericForwardAngleLift,reindexedPoint] using
      htheta.trans_le (le_of_eq hang.symm)
  · have hang :=
      F.angle_first_eq_abs hiy hyxlt
    have htheta' :
        |projectionLiftedAngle (genericProjectionSlope p)
            (p y.toOriginal - p i.toOriginal) -
          projectionLiftedAngle (genericProjectionSlope p)
            (p x.toOriginal - p i.toOriginal)| < lam := by
      simpa [abs_sub_comm] using htheta
    have h :=
      htheta'.trans_le (le_of_eq hang.symm)
    simpa [F,genericForwardAngleLift,reindexedPoint,
      EuclideanGeometry.angle_comm] using h

theorem same_standardBand_common_last_angle_lt_lam
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {x y i : ProjectionOrdered V}
    (hxi : x < i)
    (hyi : y < i)
    (hxy : x ≠ y)
    (heq :
      let D :=
        genericDirectionData_sendov hp hcap
          (sendov_scale_pos hn hdelta0 ht) hlam
      let R :=
        DirectionData.standardResidualColoring D n
          (by rw [ht]; push_cast; linarith)
      R.color x i = R.color y i) :
    EuclideanGeometry.angle
        (reindexedPoint p x) (reindexedPoint p i) (reindexedPoint p y)
      < lam := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htpos := sendov_scale_pos hn hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hwidth : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let R := DirectionData.standardResidualColoring D n hwidth
  let F := genericForwardAngleLift hp

  have heq' : R.color x i = R.color y i := by
    simpa [D,R] using heq
  let c : Fin (n+1) := R.color x i
  have hxBand :
      ((c : Fin (n+1)) : ℝ) ≤ D.value x i ∧
      D.value x i < ((c : Fin (n+1)) : ℝ) + 1 := by
    apply
      (DirectionData.standardBandColor_eq_iff
        D (n+1) (Nat.succ_pos n)
        (by exact_mod_cast hwidth)
        hxi c).1
    rfl
  have hyBand :
      ((c : Fin (n+1)) : ℝ) ≤ D.value y i ∧
      D.value y i < ((c : Fin (n+1)) : ℝ) + 1 := by
    apply
      (DirectionData.standardBandColor_eq_iff
        D (n+1) (Nat.succ_pos n)
        (by exact_mod_cast hwidth)
        hyi c).1
    simpa [c] using heq'.symm
  have hval :
      |D.value x i - D.value y i| < 1 := by
    rw [abs_lt]
    constructor <;> linarith

  have htheta :
      |projectionLiftedAngle (genericProjectionSlope p)
          (p i.toOriginal - p x.toOriginal) -
        projectionLiftedAngle (genericProjectionSlope p)
          (p i.toOriginal - p y.toOriginal)| < lam := by
    rw [genericDirectionData_sendov_value
          hp hcap htpos hlam x i,
        genericDirectionData_sendov_value
          hp hcap htpos hlam y i] at hval
    have hre :
        ((projectionLiftedAngle (genericProjectionSlope p)
            (p i.toOriginal - p x.toOriginal) -
          projectionAngleBase (genericProjectionSlope p)) / lam) -
        ((projectionLiftedAngle (genericProjectionSlope p)
            (p i.toOriginal - p y.toOriginal) -
          projectionAngleBase (genericProjectionSlope p)) / lam)
        =
        (projectionLiftedAngle (genericProjectionSlope p)
            (p i.toOriginal - p x.toOriginal) -
         projectionLiftedAngle (genericProjectionSlope p)
            (p i.toOriginal - p y.toOriginal)) / lam := by
      ring
    rw [hre, abs_div, abs_of_pos hlampos] at hval
    exact (div_lt_one hlampos).mp hval

  rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
  · have hang :=
      F.angle_last_eq_abs hxylt hyi
    have h :=
      htheta.trans_le (le_of_eq hang.symm)
    simpa [F,genericForwardAngleLift,reindexedPoint] using h
  · have hang :=
      F.angle_last_eq_abs hyxlt hxi
    have htheta' :
        |projectionLiftedAngle (genericProjectionSlope p)
            (p i.toOriginal - p y.toOriginal) -
          projectionLiftedAngle (genericProjectionSlope p)
            (p i.toOriginal - p x.toOriginal)| < lam := by
      simpa [abs_sub_comm] using htheta
    have h :=
      htheta'.trans_le (le_of_eq hang.symm)
    simpa [F,genericForwardAngleLift,reindexedPoint,
      EuclideanGeometry.angle_comm] using h

#print axioms same_standardBand_common_first_angle_lt_lam
#print axioms same_standardBand_common_last_angle_lt_lam

end ProjectionOrdered
end JSP000404Research
