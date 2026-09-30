import JSP000404Research.MiddleHiddenCrossAngle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-!
# Cluster separation in the middle-hidden five-ray pattern

Consider the cyclic ray pattern

  top, r, b, c, d

at one centre.  Suppose the two zero-quotient edges r-b and c-d have total
angle at most delta*lambda, while the three positive-transition edges

  top-r, b-c, d-top

are all strictly larger than (1+delta)*lambda.

Then every angle joining different clusters in

  {top}, {r,b}, {c,d}

is strictly larger than lambda.  The only pairs not forced above lambda are
the two zero-quotient pairs r-b and c-d.

This is a gauge-free geometric summary of the saturated middle-hidden
support-three terminal.
-/

namespace JSP000404Research

theorem middle_hidden_cluster_separation
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hlampos : 0 < lam)
    {i top r b c d : V}
    (hsmall :
      EuclideanGeometry.angle (p r) (p i) (p b) +
        EuclideanGeometry.angle (p c) (p i) (p d)
        ≤ delta * lam)
    (hTopR :
      (1 + delta) * lam <
        EuclideanGeometry.angle (p top) (p i) (p r))
    (hBridge :
      (1 + delta) * lam <
        EuclideanGeometry.angle (p b) (p i) (p c))
    (hDTop :
      (1 + delta) * lam <
        EuclideanGeometry.angle (p d) (p i) (p top)) :
    lam < EuclideanGeometry.angle (p top) (p i) (p r)
      ∧
    lam < EuclideanGeometry.angle (p top) (p i) (p b)
      ∧
    lam < EuclideanGeometry.angle (p top) (p i) (p c)
      ∧
    lam < EuclideanGeometry.angle (p top) (p i) (p d)
      ∧
    lam < EuclideanGeometry.angle (p r) (p i) (p c)
      ∧
    lam < EuclideanGeometry.angle (p r) (p i) (p d)
      ∧
    lam < EuclideanGeometry.angle (p b) (p i) (p c)
      ∧
    lam < EuclideanGeometry.angle (p b) (p i) (p d) := by
  have hrb0 :
      0 ≤ EuclideanGeometry.angle (p r) (p i) (p b) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hcd0 :
      0 ≤ EuclideanGeometry.angle (p c) (p i) (p d) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hrbSmall :
      EuclideanGeometry.angle (p r) (p i) (p b)
        ≤ delta * lam := by
    linarith
  have hcdSmall :
      EuclideanGeometry.angle (p c) (p i) (p d)
        ≤ delta * lam := by
    linarith

  have hTopBPath :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p i) (p top) (p r) (p b)
  have hTopB :
      lam < EuclideanGeometry.angle (p top) (p i) (p b) := by
    nlinarith

  have hTopCPath :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p i) (p top) (p d) (p c)
  have hcommTopD :
      EuclideanGeometry.angle (p top) (p i) (p d) =
        EuclideanGeometry.angle (p d) (p i) (p top) :=
    EuclideanGeometry.angle_comm _ _ _
  have hcommDC :
      EuclideanGeometry.angle (p d) (p i) (p c) =
        EuclideanGeometry.angle (p c) (p i) (p d) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcommTopD, hcommDC] at hTopCPath
  have hTopC :
      lam < EuclideanGeometry.angle (p top) (p i) (p c) := by
    nlinarith

  have hTopR' :
      lam < EuclideanGeometry.angle (p top) (p i) (p r) := by
    nlinarith
  have hTopD :
      lam < EuclideanGeometry.angle (p top) (p i) (p d) := by
    rw [hcommTopD]
    nlinarith

  obtain ⟨hRC,hBD,hRD,hBC⟩ :=
    middle_hidden_cross_angles_gt_lam
      (p := p) hdelta0 hlampos hsmall hBridge

  exact ⟨hTopR',hTopB,hTopC,hTopD,
    hRC,hRD,hBC,hBD⟩

#print axioms middle_hidden_cluster_separation

end JSP000404Research
