import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Quotient arithmetic in the support-three middle-hidden shape

This file deliberately isolates the finite arithmetic from the older geometric
dependency stack.

For a quotient cycle whose total sum is n, suppose some rotation has the
six-point middle-hidden shape

  [qFirst, 0, qHidden, 0, qLast].

Then

  qFirst + qHidden + qLast = n.

If the three displayed entries are positive, each is at most n-2.  A later
geometric bridge only has to supply the already-known deficit-three identity

  quotientList.sum = n

and the rotated middle-hidden shape.
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
    (qs : List ℕ)
    {n k qFirst qHidden qLast : ℕ}
    (hsum : qs.sum = n)
    (hqrot :
      qs.rotate k =
        qFirst :: 0 :: qHidden :: 0 :: qLast :: []) :
    qFirst + qHidden + qLast = n := by
  have hrotEq :
      (qs.rotate k).sum = qs.sum :=
    (List.rotate_perm qs k).sum_eq
  have hrotSum :
      (qs.rotate k).sum = n := by
    rw [hrotEq]
    exact hsum
  rw [hqrot] at hrotSum
  omega

theorem middle_hidden_each_positive_quotient_le_n_sub_two
    (qs : List ℕ)
    {n k qFirst qHidden qLast : ℕ}
    (hsum : qs.sum = n)
    (hqrot :
      qs.rotate k =
        qFirst :: 0 :: qHidden :: 0 :: qLast :: [])
    (hFirst : 1 ≤ qFirst)
    (hHidden : qHidden ≠ 0)
    (hLast : 1 ≤ qLast) :
    qFirst ≤ n - 2 ∧ qHidden ≤ n - 2 ∧ qLast ≤ n - 2 := by
  have hsum3 :=
    middle_hidden_quotients_sum_eq_n
      qs hsum hqrot
  exact three_positive_sum_eq_n_each_le_n_sub_two
    hFirst (Nat.one_le_iff_ne_zero.mpr hHidden) hLast hsum3

#print axioms three_positive_sum_eq_n_each_le_n_sub_two
#print axioms middle_hidden_quotients_sum_eq_n
#print axioms middle_hidden_each_positive_quotient_le_n_sub_two

end JSP000404Research
