import JSP000404Research.SharpCentre
import Mathlib.Tactic

/-!
# Outer-angle lower bounds around a sharp centre

Let s be SharpAt with width delta*lambda under a global angle cap pi-lambda.

For any two other points a,b, the triangle s-a-b has

  angle at s <= delta*lambda,
  angle at b <= pi-lambda.

Since the three angles sum to pi, the remaining angle at a is at least

  (1-delta)*lambda.

The symmetric statement holds at b.

In the lower branch delta<1/2 these outer angles are strictly larger than
delta*lambda.  This is the basic separator used in the four-centre terminal:
a very short quotient-zero projective gap at an outer deficit-two centre
cannot involve the ray to the sharp centre.
-/

namespace JSP000404Research

open Real

theorem outer_angle_ge_one_sub_delta_mul_lam_of_sharp
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (hs : SharpAt p delta lam s) :
    (1 - delta) * lam ≤
      EuclideanGeometry.angle (p s) (p a) (p b) := by
  have hsharp :
      EuclideanGeometry.angle (p a) (p s) (p b) ≤
        delta * lam :=
    hs a b hsa.symm hsb.symm hab
  have hcapB :
      EuclideanGeometry.angle (p s) (p b) (p a) ≤
        Real.pi - lam :=
    hcap s b a hsb hab hsa.symm
  have hsum :
      EuclideanGeometry.angle (p a) (p s) (p b) +
        EuclideanGeometry.angle (p s) (p b) (p a) +
        EuclideanGeometry.angle (p b) (p a) (p s) =
          Real.pi := by
    simpa [add_assoc, add_left_comm, add_comm] using
      (EuclideanGeometry.angle_add_angle_add_angle_eq_pi
        (p₁ := p a) (p₂ := p s) (p b)
        (hp.ne hsa.symm))
  have hcomm :
      EuclideanGeometry.angle (p b) (p a) (p s) =
        EuclideanGeometry.angle (p s) (p a) (p b) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcomm] at hsum
  linarith

theorem both_outer_angles_ge_of_sharp
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (hs : SharpAt p delta lam s) :
    (1 - delta) * lam ≤
        EuclideanGeometry.angle (p s) (p a) (p b) ∧
      (1 - delta) * lam ≤
        EuclideanGeometry.angle (p s) (p b) (p a) := by
  constructor
  · exact outer_angle_ge_one_sub_delta_mul_lam_of_sharp
      hp hcap hsa hsb hab hs
  · exact outer_angle_ge_one_sub_delta_mul_lam_of_sharp
      hp hcap hsb hsa hab.symm hs

theorem delta_mul_lam_lt_outer_angle_of_sharp
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hdelta : delta < (1 : ℝ) / 2)
    (hlam : 0 < lam)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (hs : SharpAt p delta lam s) :
    delta * lam <
      EuclideanGeometry.angle (p s) (p a) (p b) := by
  have houter :=
    outer_angle_ge_one_sub_delta_mul_lam_of_sharp
      hp hcap hsa hsb hab hs
  have hstrict :
      delta * lam < (1 - delta) * lam := by
    nlinarith
  exact hstrict.trans_le houter

#print axioms outer_angle_ge_one_sub_delta_mul_lam_of_sharp
#print axioms both_outer_angles_ge_of_sharp
#print axioms delta_mul_lam_lt_outer_angle_of_sharp

end JSP000404Research
