import JSP000404Research.SharpCentre
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-!
# Cross-angle amplification from a middle-hidden matching

Suppose four rays a,b,c,d around one centre satisfy

  angle(a,b) + angle(c,d) <= delta*lambda

while the bridge b-c satisfies

  angle(b,c) > (1+delta)*lambda.

Angular triangle inequalities then imply that every cross angle between the
two small pairs {a,b} and {c,d} is strictly larger than lambda.

This lemma is independent of the quotient construction.  It is the geometric
payoff of retaining the hidden large bridge together with the two zero-gap
matching edges.
-/

namespace JSP000404Research

theorem middle_hidden_cross_angles_gt_lam
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hlampos : 0 < lam)
    {i a b c d : V}
    (hsmall :
      EuclideanGeometry.angle (p a) (p i) (p b) +
        EuclideanGeometry.angle (p c) (p i) (p d)
        ≤ delta * lam)
    (hlarge :
      (1 + delta) * lam <
        EuclideanGeometry.angle (p b) (p i) (p c)) :
    lam < EuclideanGeometry.angle (p a) (p i) (p c)
      ∧
    lam < EuclideanGeometry.angle (p b) (p i) (p d)
      ∧
    lam < EuclideanGeometry.angle (p a) (p i) (p d)
      ∧
    lam < EuclideanGeometry.angle (p b) (p i) (p c) := by
  have hab0 :
      0 ≤ EuclideanGeometry.angle (p a) (p i) (p b) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hcd0 :
      0 ≤ EuclideanGeometry.angle (p c) (p i) (p d) :=
    EuclideanGeometry.angle_nonneg _ _ _

  have habSmall :
      EuclideanGeometry.angle (p a) (p i) (p b) ≤
        delta * lam := by
    linarith
  have hcdSmall :
      EuclideanGeometry.angle (p c) (p i) (p d) ≤
        delta * lam := by
    linarith

  have hpathAC :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p i) (p b) (p a) (p c)
  have hcommBA :
      EuclideanGeometry.angle (p b) (p i) (p a) =
        EuclideanGeometry.angle (p a) (p i) (p b) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcommBA] at hpathAC

  have hpathBD :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p i) (p b) (p d) (p c)
  have hcommDC :
      EuclideanGeometry.angle (p d) (p i) (p c) =
        EuclideanGeometry.angle (p c) (p i) (p d) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcommDC] at hpathBD

  have hpathBAtoC :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p i) (p b) (p a) (p c)
  rw [hcommBA] at hpathBAtoC
  have hpathACviaD :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p i) (p a) (p d) (p c)
  rw [hcommDC] at hpathACviaD

  have hAC :
      lam < EuclideanGeometry.angle (p a) (p i) (p c) := by
    nlinarith
  have hBD :
      lam < EuclideanGeometry.angle (p b) (p i) (p d) := by
    nlinarith
  have hAD :
      lam < EuclideanGeometry.angle (p a) (p i) (p d) := by
    nlinarith
  have hBC :
      lam < EuclideanGeometry.angle (p b) (p i) (p c) := by
    nlinarith

  exact ⟨hAC,hBD,hAD,hBC⟩

#print axioms middle_hidden_cross_angles_gt_lam

end JSP000404Research
