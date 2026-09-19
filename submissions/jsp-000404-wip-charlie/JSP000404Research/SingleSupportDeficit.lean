import JSP000404Research.GapRemainder
import JSP000404Research.UniqueGap
import Mathlib.Tactic

/-!
# General one-support Sendov centres

The unit-deficit case is only the sharpest instance of a more general rigid
family.  If the quotient vector has exactly one positive coordinate, then

  floorExcess q = (sum q) - 1

and hence, whenever sum q <= n,

  ell = n - floorExcess q = (n - sum q) + 1.

Thus a one-support centre has floor defect exactly ell-1.  Its entire
quotient-zero complement is paid for by the fractional budget

  delta + ell - 1.

After cutting at the unique positive gap, this is the normalized width of the
remaining projective ray chain.  Combined with the signed-gap cap, it is the
natural exposed/hull-centre bridge for high-exponent one-support centres.
-/

namespace JSP000404Research

open scoped BigOperators

/-- One positive quotient coordinate contributes exactly one less than the
total quotient mass to floorExcess. -/
theorem floorExcess_eq_sum_sub_one_of_support_one
    {I : Type*} [Fintype I]
    (q : I → ℕ)
    (hsupport : positiveSupport q = 1) :
    floorExcess q = (∑ i, q i) - 1 := by
  have hid := floorExcess_add_positiveSupport q
  rw [hsupport] at hid
  omega

/-- Deficit formula for a general one-support centre. -/
theorem deficit_eq_floorDefect_add_one_of_support_one
    {I : Type*} [Fintype I]
    (q : I → ℕ) (n ell : ℕ)
    (hQ : (∑ i, q i) ≤ n)
    (hsupport : positiveSupport q = 1)
    (hell : ell = n - floorExcess q) :
    ell = (n - ∑ i, q i) + 1 := by
  have hdec := deficit_eq_floorDefect_add_support q n hQ
  rw [hsupport, hell] at hdec
  exact hdec

/-- Equivalently, the integer floor defect is ell-1. -/
theorem floorDefect_eq_deficit_sub_one_of_support_one
    {I : Type*} [Fintype I]
    (q : I → ℕ) (n ell : ℕ)
    (hQ : (∑ i, q i) ≤ n)
    (hsupport : positiveSupport q = 1)
    (hell : ell = n - floorExcess q) :
    n - ∑ i, q i = ell - 1 := by
  have h :=
    deficit_eq_floorDefect_add_one_of_support_one
      q n ell hQ hsupport hell
  omega

/-- The zero-quotient complement of a one-support centre has normalized
scaled width at most delta + ell - 1. -/
theorem one_support_zero_gap_budget
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n ell : ℕ) (delta t : ℝ)
    (ht : t = (n : ℝ) + delta)
    (hgap : (∑ i, gap i) = 1)
    (hQ : (∑ i, q i) ≤ n)
    (hsupport : positiveSupport q = 1)
    (hell : ell = n - floorExcess q)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i) :
    t * zeroGapMass gap q ≤ delta + (ell - 1 : ℕ) := by
  have hb :=
    zeroGapMass_scaled_le_delta_add_deficit_sub_support
      gap q n ell delta t ht hgap hQ hell hfloor
  rw [hsupport] at hb
  exact hb

/-- One-support also gives a unique exceptional quotient-positive gap. -/
theorem existsUnique_positive_of_one_support
    {I : Type*} [Fintype I]
    (q : I → ℕ)
    (hsupport : positiveSupport q = 1) :
    ∃! e, q e ≠ 0 :=
  existsUnique_positive_of_support_one q hsupport

#print axioms floorExcess_eq_sum_sub_one_of_support_one
#print axioms deficit_eq_floorDefect_add_one_of_support_one
#print axioms floorDefect_eq_deficit_sub_one_of_support_one
#print axioms one_support_zero_gap_budget
#print axioms existsUnique_positive_of_one_support

end JSP000404Research
