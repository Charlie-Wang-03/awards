import JSP000404Research.DeficitThree
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Concrete deficit-three classification

At a concrete centre in the lower Sendov normalization, exponent n-3 means
deficit three.  For n>=4 this gives exactly the three quotient-support shapes

  support 1, quotient sum n-2;
  support 2, quotient sum n-1;
  support 3, quotient sum n.

This is the centre-level API used by the third tail layer.
-/

namespace JSP000404Research

open scoped BigOperators

theorem concrete_deficit_three_structure
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 3) :
    (positiveSupport (centreQuotient C t) = 1 ∧
      (∑ r, centreQuotient C t r) = n - 2) ∨
    (positiveSupport (centreQuotient C t) = 2 ∧
      (∑ r, centreQuotient C t r) = n - 1) ∨
    (positiveSupport (centreQuotient C t) = 3 ∧
      (∑ r, centreQuotient C t r) = n) := by
  have hQ :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hell :
      n - floorExcess (centreQuotient C t) = 3 := by
    change n - centreExponent C t = 3
    rw [hexp]
    omega
  exact deficit_three_structure
    (centreQuotient C t) n hn hQ hell

theorem deficit_three_support_one_sum
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 3)
    (hsupport : positiveSupport (centreQuotient C t) = 1) :
    (∑ r, centreQuotient C t r) = n - 2 := by
  rcases concrete_deficit_three_structure
      C hn hdelta0 hdelta1 ht hexp with h1 | h2 | h3
  · exact h1.2
  · rw [hsupport] at h2
    omega
  · rw [hsupport] at h3
    omega

theorem deficit_three_support_two_sum
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 3)
    (hsupport : positiveSupport (centreQuotient C t) = 2) :
    (∑ r, centreQuotient C t r) = n - 1 := by
  rcases concrete_deficit_three_structure
      C hn hdelta0 hdelta1 ht hexp with h1 | h2 | h3
  · rw [hsupport] at h1
    omega
  · exact h2.2
  · rw [hsupport] at h3
    omega

theorem deficit_three_support_three_sum
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 3)
    (hsupport : positiveSupport (centreQuotient C t) = 3) :
    (∑ r, centreQuotient C t r) = n := by
  rcases concrete_deficit_three_structure
      C hn hdelta0 hdelta1 ht hexp with h1 | h2 | h3
  · rw [hsupport] at h1
    omega
  · rw [hsupport] at h2
    omega
  · exact h3.2

theorem deficit_three_support_three_list_sum
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 3)
    (hsupport : positiveSupport (centreQuotient C t) = 3) :
    (quotientList t C.gaps).sum = n := by
  rw [← centreQuotient_sum_eq_list_sum C t]
  exact deficit_three_support_three_sum
    C hn hdelta0 hdelta1 ht hexp hsupport

#print axioms concrete_deficit_three_structure
#print axioms deficit_three_support_one_sum
#print axioms deficit_three_support_two_sum
#print axioms deficit_three_support_three_sum

end JSP000404Research
