import JSP000404Research.GeneralMixedExteriorActualHull
import JSP000404Research.GeneralMixedInteriorContradiction
import Mathlib.Tactic

/-!
# Arbitrary finite mixed pattern: the exact hidden-angle frontier

The genuine sharp/support-one/support-two centre hypotheses force any
fourth centre into the distinguished triangle, by the kernel-checked
cardinality-free exterior theorem.

For a fourth centre inside that triangle, the separately proved
cardinality-free interior contradiction excludes any hidden angle
at b at least ((n-1)-delta)*lambda.

Thus, in EVERY finite ambient configuration under the genuine
AngleCap/centreExponent/positiveSupport hypotheses, the hidden angle
at b is STRICTLY BELOW that threshold.  This is the exact surviving
geometric frontier, not a global six-source Boolean payment.

No new support interval witness, global Hall certificate, or
nondisjoint dyadic credit is assumed in this theorem.
-/

namespace JSP000404Research

theorem general_mixed_hidden_angle_strict_upper
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
    EuclideanGeometry.angle (p s) (p b) (p c) <
      (((n - 1 : ℕ) : ℝ) - delta) * lam := by
  have hinside :
      p c ∈ convexHull ℝ ({p s, p a, p b} : Set Plane) :=
    mixed_fourth_mem_triangle_of_actual_pattern
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      Cs Ca Cb hS hA hB hsupA hsupB
  by_contra hnot
  have hlarge :
      (((n - 1 : ℕ) : ℝ) - delta) * lam ≤
        EuclideanGeometry.angle (p s) (p b) (p c) :=
    le_of_not_gt hnot
  exact no_mixed_fourth_inside_of_weakened_hidden_angle
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hab hac hbc hinside hlarge

/-- A concrete lower bound matching the threshold therefore excludes
the genuine mixed pattern in any finite ambient point set. -/
theorem no_general_mixed_pattern_of_hidden_angle_lower
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
    (hsupB : positiveSupport (centreQuotient Cb t) = 2)
    (hlarge :
      (((n - 1 : ℕ) : ℝ) - delta) * lam ≤
        EuclideanGeometry.angle (p s) (p b) (p c)) :
    False := by
  have hstrict :=
    general_mixed_hidden_angle_strict_upper
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      Cs Ca Cb hS hA hB hsupA hsupB
  exact not_lt_of_ge hlarge hstrict

#print axioms general_mixed_hidden_angle_strict_upper
#print axioms no_general_mixed_pattern_of_hidden_angle_lower

end JSP000404Research
