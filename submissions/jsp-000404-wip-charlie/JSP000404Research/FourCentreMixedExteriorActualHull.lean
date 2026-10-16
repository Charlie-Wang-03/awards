import JSP000404Research.FourCentreMixedExteriorContradiction
import Mathlib.Tactic

/-!
# Actual sharp/support-one/support-two mixed four-centre hull constraint

This is the direct positive formulation of the (independently verified)
mixed-exterior exclusion: the original geometric exponent and quotient-support
premises imply that the fourth centre is in the triangle of the three
distinguished high-exponent centres.

Unlike the preceding geometric frontier, the statement does not require a
caller to supply HighExponentTransitionIntervalCertificate objects or
to separately prove that their quotient costs sum to 2*n.  Those
connections are handled by FourCentreTransitionCases and the exterior
contradiction theorem in the imports.  This merely exposes the
already-proved implication for the subsequent interior branch.
-/

namespace JSP000404Research

theorem mixed_fourth_mem_triangle_of_actual_sharp_support_pattern
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c : Fin 4}
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
  exact no_mixed_fourth_outside_triangle_fin_four
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hab hac hbc
    Cs Ca Cb hS hA hB hsupA hsupB hout

#print axioms mixed_fourth_mem_triangle_of_actual_sharp_support_pattern

end JSP000404Research
