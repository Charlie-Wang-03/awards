import JSP000404Research.NoTopTwoNextMultiplicity
import Mathlib.Tactic

/-!
# Sharp Fin 4 terminal follows from genuine arbitrary-finite exclusion

The original two legacy theorems are retained, with the same hypotheses and
conclusions. Their previous proofs split the fourth point into inside/outside
geometric cases and the support patterns into mixed cases. The stronger
kernel-checked `no_top_and_two_next_with_fourth` excludes the entire
configuration immediately, without an auxiliary inside/outside assumption.

The global six-source dyadic payment remains a separate open obligation.
-/

namespace JSP000404Research

theorem no_sharp_mixed_support_one_two_fin_four
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
  exact no_top_and_two_next_with_fourth
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hab hac hbc Cs Ca Cb hS hA hB


/-- Final structural statement for four centres: a unit-deficit centre cannot
have two distinct deficit-two companions. -/
theorem no_sharp_with_two_deficit_two_fin_four
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
    (hB : centreExponent Cb t = n - 2) :
    False := by
  exact no_top_and_two_next_with_fourth
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hab hac hbc Cs Ca Cb hS hA hB


#print axioms no_sharp_mixed_support_one_two_fin_four
#print axioms no_sharp_with_two_deficit_two_fin_four

end JSP000404Research
