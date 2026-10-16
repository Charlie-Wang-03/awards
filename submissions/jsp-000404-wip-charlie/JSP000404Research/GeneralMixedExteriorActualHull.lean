import JSP000404Research.GeneralMixedExteriorContradiction
import Mathlib.Tactic

/-!
# Arbitrary finite mixed-centre hull inclusion, without fabricated credits

This is the positive hull-membership interface for the kernel-checked
arbitrary finite-cardinality mixed-exterior exclusion. It keeps the actual
centreExponent / quotient-support premises; it is not another independent
geometric estimate and does not solve the six-source global payment.
-/

namespace JSP000404Research

theorem mixed_fourth_mem_triangle_of_actual_pattern
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
    p c ∈ convexHull ℝ ({p s, p a, p b} : Set Plane) := by
  by_contra hout
  exact no_mixed_fourth_outside_triangle
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hab hac hbc Cs Ca Cb
    hS hA hB hsupA hsupB hout

#print axioms mixed_fourth_mem_triangle_of_actual_pattern

end JSP000404Research
