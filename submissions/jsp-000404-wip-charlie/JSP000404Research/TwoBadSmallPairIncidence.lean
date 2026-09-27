import JSP000404Research.TwoSmallAngleMixed
import Mathlib.Tactic

/-!
# Common-triangle terminal for two bad-minimum small-angle witnesses

All remaining support-2/3 pair cases reduce to the same geometric endpoint
pattern.  If centres a and b share a third minimum z such that

  angle(b,a,z) <= alpha*lambda,
  angle(a,b,z) <= beta*lambda,

and alpha+beta<1, the angle cap is impossible.

The lower-branch coefficients used later are

  support 2 : (1+delta)/3,
  support 3 : delta.

For delta<1/2, every 2/2, 2/3, and 3/3 coefficient sum is strictly below one.
This file isolates the endpoint-incidence terminal from the combinatorial
work needed to force that incidence.
-/

namespace JSP000404Research

theorem impossible_cross_incident_small_pairs
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam alpha beta : ℝ}
    (hlam : 0 < lam)
    (hsum : alpha + beta < 1)
    {a b z : V}
    (hab : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (ha :
      EuclideanGeometry.angle (p b) (p a) (p z)
        ≤ alpha * lam)
    (hb :
      EuclideanGeometry.angle (p a) (p b) (p z)
        ≤ beta * lam) :
    False :=
  impossible_two_scaled_small_angles_under_cap
    hp hcap hsum hlam hab haz hbz ha hb

theorem support_three_three_coeff_sum_lt_one
    {delta : ℝ}
    (hdeltaHalf : delta < (1 : ℝ) / 2) :
    delta + delta < (1 : ℝ) := by
  linarith

theorem impossible_support_two_two_cross_incidence
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam delta : ℝ}
    (hlam : 0 < lam)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    {a b z : V}
    (hab : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (ha :
      EuclideanGeometry.angle (p b) (p a) (p z)
        ≤ ((1 + delta) / 3) * lam)
    (hb :
      EuclideanGeometry.angle (p a) (p b) (p z)
        ≤ ((1 + delta) / 3) * lam) :
    False :=
  impossible_cross_incident_small_pairs
    hp hcap hlam
    (two_support_two_coeff_sum_lt_one hdeltaHalf)
    hab haz hbz ha hb

theorem impossible_support_two_three_cross_incidence
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam delta : ℝ}
    (hlam : 0 < lam)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    {a b z : V}
    (hab : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (ha :
      EuclideanGeometry.angle (p b) (p a) (p z)
        ≤ ((1 + delta) / 3) * lam)
    (hb :
      EuclideanGeometry.angle (p a) (p b) (p z)
        ≤ delta * lam) :
    False :=
  impossible_cross_incident_small_pairs
    hp hcap hlam
    (support_two_three_coeff_sum_lt_one hdeltaHalf)
    hab haz hbz ha hb

theorem impossible_support_three_two_cross_incidence
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam delta : ℝ}
    (hlam : 0 < lam)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    {a b z : V}
    (hab : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (ha :
      EuclideanGeometry.angle (p b) (p a) (p z)
        ≤ delta * lam)
    (hb :
      EuclideanGeometry.angle (p a) (p b) (p z)
        ≤ ((1 + delta) / 3) * lam) :
    False := by
  exact impossible_cross_incident_small_pairs
    hp hcap hlam
    (by
      have h :=
        support_two_three_coeff_sum_lt_one hdeltaHalf
      linarith)
    hab haz hbz ha hb

theorem impossible_support_three_three_cross_incidence
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam delta : ℝ}
    (hlam : 0 < lam)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    {a b z : V}
    (hab : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (ha :
      EuclideanGeometry.angle (p b) (p a) (p z)
        ≤ delta * lam)
    (hb :
      EuclideanGeometry.angle (p a) (p b) (p z)
        ≤ delta * lam) :
    False :=
  impossible_cross_incident_small_pairs
    hp hcap hlam
    (support_three_three_coeff_sum_lt_one hdeltaHalf)
    hab haz hbz ha hb

#print axioms impossible_cross_incident_small_pairs
#print axioms impossible_support_two_two_cross_incidence
#print axioms impossible_support_two_three_cross_incidence
#print axioms impossible_support_three_three_cross_incidence

end JSP000404Research
