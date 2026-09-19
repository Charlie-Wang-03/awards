import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Zero-carry decomposition for Sendov gap exponents

This file isolates the elementary natural-number identity behind the
`ell = a + p` decomposition used in the JSP-000404 research route.

For a finite family of nonnegative integer gap quotients `q i`:
* `floorExcess q = sum (q i - 1)`;
* `positiveSupport q` counts the indices with `q i > 0`.

Then
`floorExcess q + positiveSupport q = sum q i`.

Consequently, whenever `sum q i <= n`,
`n - floorExcess q = (n - sum q i) + positiveSupport q`.
This is the exact abstract form of `ell_i = a_i + p_i`.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Sum of the positive parts `(q_i - 1)_+` for natural `q_i`. -/
def floorExcess {I : Type*} [Fintype I] (q : I → ℕ) : ℕ :=
  ∑ i, (q i - 1)

/-- Number of indices on which `q_i` is positive. -/
def positiveSupport {I : Type*} [Fintype I] (q : I → ℕ) : ℕ :=
  ∑ i, if q i = 0 then 0 else 1

/-- Removing one unit from every positive entry and then restoring one unit
per positive entry recovers the original sum exactly. -/
theorem floorExcess_add_positiveSupport
    {I : Type*} [Fintype I] (q : I → ℕ) :
    floorExcess q + positiveSupport q = ∑ i, q i := by
  classical
  unfold floorExcess positiveSupport
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hq : q i = 0
  · simp [hq]
  · have hpos : 1 ≤ q i := Nat.one_le_iff_ne_zero.mpr hq
    simp [hq, Nat.sub_add_cancel hpos]

/-- The floor-excess sum never exceeds the original quotient sum. -/
theorem floorExcess_le_sum
    {I : Type*} [Fintype I] (q : I → ℕ) :
    floorExcess q ≤ ∑ i, q i := by
  have h := floorExcess_add_positiveSupport q
  omega

/-- Exact zero-carry / support decomposition of the deficit.

In the Sendov application, `sum q i` is `Q_i`,
`floorExcess q` is `k_i`, and the left-hand side is `ell_i = n-k_i`.
-/
theorem deficit_eq_floorDefect_add_support
    {I : Type*} [Fintype I] (q : I → ℕ) (n : ℕ)
    (hQ : (∑ i, q i) ≤ n) :
    n - floorExcess q =
      (n - ∑ i, q i) + positiveSupport q := by
  have hid := floorExcess_add_positiveSupport q
  omega

/-- The number of positive quotient gaps is at most the total deficit. -/
theorem positiveSupport_le_deficit
    {I : Type*} [Fintype I] (q : I → ℕ) (n : ℕ)
    (hQ : (∑ i, q i) ≤ n) :
    positiveSupport q ≤ n - floorExcess q := by
  rw [deficit_eq_floorDefect_add_support q n hQ]
  omega

/-- If the total deficit is at most `r`, then at most `r` quotient gaps
can be positive.  This is the combinatorial content needed when a high
Sendov exponent forces a small number of large angular gaps. -/
theorem positiveSupport_le_of_deficit_le
    {I : Type*} [Fintype I] (q : I → ℕ) (n r : ℕ)
    (hQ : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q ≤ r) :
    positiveSupport q ≤ r :=
  (positiveSupport_le_deficit q n hQ).trans hell

#print axioms floorExcess_add_positiveSupport
#print axioms floorExcess_le_sum
#print axioms deficit_eq_floorDefect_add_support
#print axioms positiveSupport_le_deficit
#print axioms positiveSupport_le_of_deficit_le

end JSP000404Research
