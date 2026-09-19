import JSP000404Research.SingleSupportDeficit
import Mathlib.Tactic

/-!
# A one-support complement is strictly shorter than a projective half-circle

Let Z be the total mass of all quotient-zero gaps at a one-support centre.
The general remainder budget gives

  t * Z <= delta + ell - 1.

If ell <= n and t = n + delta with n >= 1, then

  delta + ell - 1 < n + delta = t.

Hence Z < 1.  Since the projective direction circle has angular length pi,
the entire zero-gap complement has angular width pi*Z < pi.

This is the quantitative width input needed by StrictExposure.
-/

namespace JSP000404Research

/-- The normalized zero-gap complement has mass strictly below one. -/
theorem one_support_zeroGapMass_lt_one
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n ell : ℕ) (delta t : ℝ)
    (hn : 1 ≤ n)
    (helln : ell ≤ n)
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hgap : (∑ i, gap i) = 1)
    (hQ : (∑ i, q i) ≤ n)
    (hsupport : positiveSupport q = 1)
    (hell : ell = n - floorExcess q)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i) :
    zeroGapMass gap q < 1 := by
  have hbudget :=
    one_support_zero_gap_budget
      gap q n ell delta t ht hgap hQ hsupport hell hfloor
  have hnat : ell - 1 < n := by
    omega
  have hnatR : ((ell - 1 : ℕ) : ℝ) < (n : ℝ) := by
    exact_mod_cast hnat
  have hrhs :
      delta + ((ell - 1 : ℕ) : ℝ) < t := by
    rw [ht]
    linarith
  have hmul :
      t * zeroGapMass gap q < t := hbudget.trans_lt hrhs
  have hmul' :
      t * zeroGapMass gap q < t * 1 := by
    simpa using hmul
  exact (mul_lt_mul_left htpos).mp hmul'

/-- Therefore the angular width of the zero-gap complement is strictly below
pi. -/
theorem one_support_zeroGap_angle_lt_pi
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n ell : ℕ) (delta t : ℝ)
    (hn : 1 ≤ n)
    (helln : ell ≤ n)
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hgap : (∑ i, gap i) = 1)
    (hQ : (∑ i, q i) ≤ n)
    (hsupport : positiveSupport q = 1)
    (hell : ell = n - floorExcess q)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i) :
    Real.pi * zeroGapMass gap q < Real.pi := by
  have hz :=
    one_support_zeroGapMass_lt_one
      gap q n ell delta t hn helln ht htpos
      hgap hQ hsupport hell hfloor
  exact mul_lt_mul_of_pos_left hz Real.pi_pos

#print axioms one_support_zeroGapMass_lt_one
#print axioms one_support_zeroGap_angle_lt_pi

end JSP000404Research
