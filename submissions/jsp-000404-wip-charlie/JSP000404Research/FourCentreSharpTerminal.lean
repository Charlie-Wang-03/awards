import JSP000404Research.FourCentreMixedExteriorContradiction
import JSP000404Research.FourCentreMixedInteriorContradiction
import JSP000404Research.FourCentreSharpReduction
import Mathlib.Tactic

/-!
# Complete closure of the sharp four-centre terminal

For one unit-deficit centre s and two deficit-two centres a,b, the support
reduction leaves only the mixed patterns (1,2) or (2,1).

For a fixed mixed orientation, the fourth point c is either outside the outer
triangle conv{s,a,b}, where the exposed-support packing contradiction applies,
or inside that triangle, where the hidden-angle contradiction applies.

Therefore no sharp centre in a four-point lower-branch configuration can have
two distinct deficit-two companions.
-/

namespace JSP000404Research

theorem no_sharp_mixed_support_one_two_fin_four
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
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
  by_cases hinside :
      p c ∈ convexHull ℝ
        ({p s, p a, p b} : Set Plane)
  · exact no_mixed_fourth_inside_fin_four
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      Cs Ca Cb hS hA hB hsupA hsupB hinside
  · exact no_mixed_fourth_outside_triangle_fin_four
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      Cs Ca Cb hS hA hB hsupA hsupB hinside

/-- Final structural statement for four centres: a unit-deficit centre cannot
have two distinct deficit-two companions. -/
theorem no_sharp_with_two_deficit_two_fin_four
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
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
    (hB : centreExponent Cb t = n - 2) :
    False := by
  rcases sharp_two_deficit_two_force_mixed_support_fin_four
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      Cs Ca Cb hS hA hB with h12 | h21
  · exact no_sharp_mixed_support_one_two_fin_four
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      Cs Ca Cb hS hA hB
      h12.1 h12.2
  · exact no_sharp_mixed_support_one_two_fin_four
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsb hsa hsc hab.symm hbc hac
      Cs Cb Ca hS hB hA
      h21.2 h21.1

#print axioms no_sharp_mixed_support_one_two_fin_four
#print axioms no_sharp_with_two_deficit_two_fin_four

end JSP000404Research
