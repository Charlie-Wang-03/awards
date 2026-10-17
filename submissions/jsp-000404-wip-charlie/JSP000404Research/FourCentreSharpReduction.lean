import JSP000404Research.FourCentreTransitionCases
import JSP000404Research.FourCentreSupportTwoContradiction
import JSP000404Research.NoTopTwoNextMultiplicity
import Mathlib.Tactic

/-!
# Legacy four-centre support classification, now closed by stronger exclusion

A centre with exponent n-2 has genuine quotient support 1 or 2.
The historical Fin 4 theorem below stated that top+two-next-layer
forces a mixed support pair. It is retained unchanged for compatibility.

The newer sorry-free `no_top_and_two_next_with_fourth` theorem excludes
ALL four support combinations in any finite configuration with a fourth
distinct centre. Consequently the historical mixed-only conclusion now
follows by contradiction. No unproved geometry is reintroduced.
-/

namespace JSP000404Research

open scoped BigOperators

theorem deficit_two_support_one_or_two_concrete
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 2) :
    positiveSupport (centreQuotient C t) = 1 ∨
      positiveSupport (centreQuotient C t) = 2 := by
  have hdelta1 : delta < 1 := by linarith
  have hQ :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega) hdelta0 hdelta1 ht
  have hdef :
      n - floorExcess (centreQuotient C t) = 2 := by
    rw [← show centreExponent C t =
      floorExcess (centreQuotient C t) by rfl, hexp]
    omega
  rcases deficit_two_structure
      (centreQuotient C t) n hn hQ hdef with h1 | h2
  · exact Or.inl h1.1
  · exact Or.inr h2.1

theorem sharp_two_deficit_two_force_mixed_support_fin_four
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
    (
      positiveSupport (centreQuotient Ca t) = 1 ∧
      positiveSupport (centreQuotient Cb t) = 2
    ) ∨
    (
      positiveSupport (centreQuotient Ca t) = 2 ∧
      positiveSupport (centreQuotient Cb t) = 1
    ) := by
  exact False.elim
    (no_top_and_two_next_with_fourth
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc Cs Ca Cb hS hA hB)

#print axioms deficit_two_support_one_or_two_concrete
#print axioms sharp_two_deficit_two_force_mixed_support_fin_four

end JSP000404Research
