import JSP000404Research.FourCentreMixedExteriorActualHull
import JSP000404Research.FourCentreMixedInteriorContradiction
import Mathlib.Tactic

/-!
# Four-centre mixed support-one/support-two geometric exclusion

The exterior branch is handled directly from the original centreExponent
and positiveSupport values, with no caller-supplied transition certificates.
The interior branch then uses the weakened hidden-angle estimate and the
two-cap short arithmetic contradiction.

This theorem is conditional on a specific four-centre mixed pattern. It
is NOT the missing arbitrary-cardinality global non-reusing payment theorem.
-/

namespace JSP000404Research

theorem no_mixed_sharp_support_one_two_fin_four
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
    False := by
  have hinside :
      p c ∈ convexHull ℝ ({p s, p a, p b} : Set Plane) :=
    mixed_fourth_mem_triangle_of_actual_sharp_support_pattern
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      Cs Ca Cb hS hA hB hsupA hsupB
  exact no_mixed_fourth_inside_fin_four
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hab hac hbc
    Cs Ca Cb hS hA hB hsupA hsupB hinside

#print axioms no_mixed_sharp_support_one_two_fin_four

end JSP000404Research
