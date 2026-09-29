import JSP000404Research.ConcreteDeficitThree
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Quotient bound in the support-three middle-hidden shape

At an exact deficit-three/support-three centre the complete quotient sum is n.
After pinning the sharp ray, the middle-hidden six-point shape is

  [qFirst, 0, qHidden, 0, qLast]

with all three displayed positive entries nonzero.

Hence

  qFirst + qHidden + qLast = n

and in particular qHidden <= n-2.  The same bound holds for either end
positive quotient.

This is the arithmetic input needed to turn a sign-transition quotient into
a genuine angle larger than (1+delta)*lambda.
-/

namespace JSP000404Research

theorem three_positive_sum_eq_n_each_le_n_sub_two
    {q₁ q₂ q₃ n : ℕ}
    (h₁ : 1 ≤ q₁)
    (h₂ : 1 ≤ q₂)
    (h₃ : 1 ≤ q₃)
    (hsum : q₁ + q₂ + q₃ = n) :
    q₁ ≤ n - 2 ∧ q₂ ≤ n - 2 ∧ q₃ ≤ n - 2 := by
  omega

theorem middle_hidden_quotients_sum_eq_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n k qFirst qHidden qLast : ℕ}
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 3)
    (hsupport : positiveSupport (centreQuotient C t) = 3)
    (hqrot :
      (quotientList t C.gaps).rotate k =
        qFirst :: 0 :: qHidden :: 0 :: qLast :: []) :
    qFirst + qHidden + qLast = n := by
  have hsum :
      (quotientList t C.gaps).sum = n :=
    deficit_three_support_three_list_sum
      C hn4 hdelta0 hdelta1 ht hexp hsupport
  have hrotSum :
      ((quotientList t C.gaps).rotate k).sum = n := by
    rw [List.sum_rotate]
    exact hsum
  rw [hqrot] at hrotSum
  simpa using hrotSum

theorem middle_hidden_each_positive_quotient_le_n_sub_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n k qFirst qHidden qLast : ℕ}
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 3)
    (hsupport : positiveSupport (centreQuotient C t) = 3)
    (hqrot :
      (quotientList t C.gaps).rotate k =
        qFirst :: 0 :: qHidden :: 0 :: qLast :: [])
    (hFirst : 1 ≤ qFirst)
    (hHidden : qHidden ≠ 0)
    (hLast : 1 ≤ qLast) :
    qFirst ≤ n - 2 ∧ qHidden ≤ n - 2 ∧ qLast ≤ n - 2 := by
  have hsum :=
    middle_hidden_quotients_sum_eq_n
      C hn4 hdelta0 hdelta1 ht hexp hsupport hqrot
  exact three_positive_sum_eq_n_each_le_n_sub_two
    hFirst (Nat.one_le_iff_ne_zero.mpr hHidden) hLast hsum

#print axioms three_positive_sum_eq_n_each_le_n_sub_two
#print axioms middle_hidden_quotients_sum_eq_n
#print axioms middle_hidden_each_positive_quotient_le_n_sub_two

end JSP000404Research
