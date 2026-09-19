import JSP000404Research.SharpDeficit
import Mathlib.Tactic

/-!
# Fractional remainder budget for Sendov gaps

Let the normalized total scale be `t = n + delta`, and write each angular
gap in the form

  `t * gap i = q i + remainder i`

with natural quotient `q i` and nonnegative remainder.  Once a unit-deficit
centre has forced `sum q = n`, the total remainder budget is exactly
`delta`.

In particular, every gap with quotient zero is paid for entirely by this
remainder budget, so the total scaled width of all zero-quotient gaps is at
most `delta`.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Total mass of the gaps whose integer quotient is zero. -/
noncomputable def zeroGapMass
    {I : Type*} [Fintype I] (gap : I → ℝ) (q : I → ℕ) : ℝ :=
  ∑ i, if q i = 0 then gap i else 0

/-- If `t = n + delta`, the gaps sum to one, and the integer quotients sum
to `n`, then the fractional remainders sum exactly to `delta`. -/
theorem remainder_sum_eq_delta
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (ht : t = (n : ℝ) + delta)
    (hgap : (∑ i, gap i) = 1)
    (hQ : (∑ i, q i) = n) :
    (∑ i, (t * gap i - (q i : ℝ))) = delta := by
  classical
  have hQcast : (∑ i, (q i : ℝ)) = (n : ℝ) := by
    exact_mod_cast hQ
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hgap, hQcast, ht]
  ring

/-- Zero-quotient gaps consume at most the whole fractional remainder budget. -/
theorem zeroGapMass_scaled_le_delta
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (ht : t = (n : ℝ) + delta)
    (hgap : (∑ i, gap i) = 1)
    (hQ : (∑ i, q i) = n)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i) :
    t * zeroGapMass gap q ≤ delta := by
  classical
  have hpoint :
      ∀ i : I,
        t * (if q i = 0 then gap i else 0) ≤
          t * gap i - (q i : ℝ) := by
    intro i
    by_cases hqi : q i = 0
    · simp [hqi]
    · have hnonneg : 0 ≤ t * gap i - (q i : ℝ) := by
        linarith [hfloor i]
      simp [hqi, hnonneg]
  have hsum :
      ∑ i, t * (if q i = 0 then gap i else 0) ≤
        ∑ i, (t * gap i - (q i : ℝ)) :=
    Finset.sum_le_sum fun i _ => hpoint i
  have hleft :
      (∑ i, t * (if q i = 0 then gap i else 0)) =
        t * zeroGapMass gap q := by
    unfold zeroGapMass
    rw [Finset.mul_sum]
  rw [hleft, remainder_sum_eq_delta gap q n delta t ht hgap hQ] at hsum
  exact hsum

/-- Dividing by a positive scale gives the ordinary zero-gap mass bound. -/
theorem zeroGapMass_le_delta_div
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hgap : (∑ i, gap i) = 1)
    (hQ : (∑ i, q i) = n)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i) :
    zeroGapMass gap q ≤ delta / t := by
  rw [le_div_iff₀ htpos]
  exact zeroGapMass_scaled_le_delta gap q n delta t ht hgap hQ hfloor

/-- General remainder identity before specializing to unit deficit.

If Q = sum q <= n, then the total fractional remainder is
delta + (n-Q). -/
theorem remainder_sum_eq_delta_add_floorDefect
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (ht : t = (n : ℝ) + delta)
    (hgap : (∑ i, gap i) = 1)
    (hQle : (∑ i, q i) ≤ n) :
    (∑ i, (t * gap i - (q i : ℝ))) =
      delta + (n - ∑ i, q i : ℕ) := by
  classical
  have hQcast :
      (∑ i, (q i : ℝ)) = ((∑ i, q i : ℕ) : ℝ) := by
    norm_num
  have hsubcast :
      (((n - ∑ i, q i : ℕ) : ℕ) : ℝ) =
        (n : ℝ) - ((∑ i, q i : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hQle
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hgap, hQcast, ht]
  push_cast
  rw [hsubcast]
  ring

/-- General zero-gap budget: all quotient-zero gaps are paid for by the
fractional remainder delta plus the integer floor defect n-Q. -/
theorem zeroGapMass_scaled_le_delta_add_floorDefect
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (ht : t = (n : ℝ) + delta)
    (hgap : (∑ i, gap i) = 1)
    (hQle : (∑ i, q i) ≤ n)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i) :
    t * zeroGapMass gap q ≤
      delta + (n - ∑ i, q i : ℕ) := by
  classical
  have hpoint :
      ∀ i : I,
        t * (if q i = 0 then gap i else 0) ≤
          t * gap i - (q i : ℝ) := by
    intro i
    by_cases hqi : q i = 0
    · simp [hqi]
    · have hnonneg : 0 ≤ t * gap i - (q i : ℝ) := by
        linarith [hfloor i]
      simp [hqi, hnonneg]
  have hsum :
      ∑ i, t * (if q i = 0 then gap i else 0) ≤
        ∑ i, (t * gap i - (q i : ℝ)) :=
    Finset.sum_le_sum fun i _ => hpoint i
  have hleft :
      (∑ i, t * (if q i = 0 then gap i else 0)) =
        t * zeroGapMass gap q := by
    unfold zeroGapMass
    rw [Finset.mul_sum]
  rw [hleft,
    remainder_sum_eq_delta_add_floorDefect gap q n delta t ht hgap hQle] at hsum
  exact hsum

/-- Express the same budget through the Sendov deficit ell=n-floorExcess.

Writing p for the number of positive quotient gaps, ell=(n-Q)+p, so the
zero-gap scaled width is at most delta+ell-p. -/
theorem zeroGapMass_scaled_le_delta_add_deficit_sub_support
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n ell : ℕ) (delta t : ℝ)
    (ht : t = (n : ℝ) + delta)
    (hgap : (∑ i, gap i) = 1)
    (hQle : (∑ i, q i) ≤ n)
    (hell : ell = n - floorExcess q)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i) :
    t * zeroGapMass gap q ≤
      delta + (ell - positiveSupport q : ℕ) := by
  have hbudget :=
    zeroGapMass_scaled_le_delta_add_floorDefect
      gap q n delta t ht hgap hQle hfloor
  have hdecomp := deficit_eq_floorDefect_add_support q n hQle
  have hsub :
      ell - positiveSupport q = n - ∑ i, q i := by
    rw [hell, hdecomp]
    omega
  rwa [hsub]

/-- Combined unit-deficit consequence: the quotient support count is one,
the quotient sum is exactly `n`, and all zero-quotient gaps together have
scaled width at most `delta`. -/
theorem unit_deficit_zero_gap_budget
    {I : Type*} [Fintype I]
    (gap : I → ℝ) (q : I → ℕ)
    (n : ℕ) (delta t : ℝ)
    (hn : 2 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (hgap : (∑ i, gap i) = 1)
    (hQle : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 1)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i) :
    positiveSupport q = 1 ∧
      (∑ i, q i) = n ∧
      t * zeroGapMass gap q ≤ delta := by
  have hs := unit_deficit_structure q n hn hQle hell
  refine ⟨hs.1, hs.2, ?_⟩
  exact zeroGapMass_scaled_le_delta gap q n delta t ht hgap hs.2 hfloor

#print axioms remainder_sum_eq_delta
#print axioms remainder_sum_eq_delta_add_floorDefect
#print axioms zeroGapMass_scaled_le_delta_add_floorDefect
#print axioms zeroGapMass_scaled_le_delta_add_deficit_sub_support
#print axioms zeroGapMass_scaled_le_delta
#print axioms zeroGapMass_le_delta_div
#print axioms unit_deficit_zero_gap_budget

end JSP000404Research
