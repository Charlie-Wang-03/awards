import JSP000404Research.GeneralMixedBaseAngleLarge
import JSP000404Research.GeneralMixedHiddenAngleFrontier
import Mathlib.Tactic

/-!
# The mixed support-one ray is separated from every fourth ray at support-two b

The already proved hidden-angle strict upper bound, together with the real
large-angle base-wedge lower bound, forces every fourth actual ray c at b to
satisfy angle(c,b,a) > delta*lambda.

This is a new nontrivial necessary geometric condition from the original
AngleCap hypotheses; it neither assumes a special witness endpoint nor uses
the unproved six-source Boolean payment.
-/

namespace JSP000404Research

theorem general_mixed_support_one_ray_delta_separated_from_fourth
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) = 2) :
    delta * lam <
      EuclideanGeometry.angle (p c) (p b) (p a) := by
  have hbase :=
    general_mixed_base_angle_large_of_actual_pattern
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hab Cs Ca Cb hS hA hB hsupA hsupB
  have hhidden :=
    general_mixed_hidden_angle_strict_upper
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      Cs Ca Cb hS hA hB hsupA hsupB
  have hcHull :=
    mixed_fourth_mem_triangle_of_actual_pattern
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      Cs Ca Cb hS hA hB hsupA hsupB
  have hsplit :
      EuclideanGeometry.angle (p s) (p b) (p a) =
        EuclideanGeometry.angle (p s) (p b) (p c) +
          EuclideanGeometry.angle (p c) (p b) (p a) :=
    angle_split_at_third_of_mem_convexHull_three
      hcHull (hp.ne hbc.symm)
  nlinarith

#print axioms general_mixed_support_one_ray_delta_separated_from_fourth

end JSP000404Research
