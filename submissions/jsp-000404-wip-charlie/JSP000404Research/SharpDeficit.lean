import JSP000404Research.ZeroCarry
import Mathlib.Tactic

/-!
# Structure of a unit Sendov deficit

The zero-carry identity becomes especially rigid when the total deficit is one.
For `n >= 2`, assuming the quotient sum is at most `n`,

`n - floorExcess q = 1`

forces both

* `positiveSupport q = 1`: exactly one unit of positive-gap support is
  available in the indicator count; and
* `sum q = n`: there is no floor-carry deficit.

This is the integer core of the geometric statement that an `ell = 1`
centre has one large projective gap and all remaining gaps are sub-unit.
-/

namespace JSP000404Research

open scoped BigOperators

/-- If the positive-support count vanishes, every quotient entry vanishes. -/
theorem positiveSupport_eq_zero_imp
    {I : Type*} [Fintype I] (q : I → ℕ)
    (hzero : positiveSupport q = 0) :
    ∀ i, q i = 0 := by
  classical
  intro i
  by_contra hqi
  have hterm :
      1 ≤ ∑ x : I, (if q x = 0 then 0 else 1) := by
    calc
      1 = (if q i = 0 then 0 else 1) := by simp [hqi]
      _ ≤ ∑ x : I, (if q x = 0 then 0 else 1) := by
        exact Finset.single_le_sum
          (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
  unfold positiveSupport at hzero
  omega

/-- A unit deficit has exactly one positive-support unit and no floor carry. -/
theorem unit_deficit_structure
    {I : Type*} [Fintype I] (q : I → ℕ) (n : ℕ)
    (hn : 2 ≤ n)
    (hQ : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 1) :
    positiveSupport q = 1 ∧ (∑ i, q i) = n := by
  have hsupport_le : positiveSupport q ≤ 1 := by
    have h := positiveSupport_le_deficit q n hQ
    omega
  have hsupport_pos : 0 < positiveSupport q := by
    by_contra hnot
    have hsupport_zero : positiveSupport q = 0 := Nat.eq_zero_of_not_pos hnot
    have hqzero := positiveSupport_eq_zero_imp q hsupport_zero
    have hexcess_zero : floorExcess q = 0 := by
      simp [floorExcess, hqzero]
    rw [hexcess_zero] at hell
    omega
  have hsupport : positiveSupport q = 1 := by omega
  have hdecomp := deficit_eq_floorDefect_add_support q n hQ
  constructor
  · exact hsupport
  · rw [hdecomp, hsupport] at hell
    omega

/-- In particular, the quotient sum of a unit-deficit centre is positive. -/
theorem unit_deficit_sum_pos
    {I : Type*} [Fintype I] (q : I → ℕ) (n : ℕ)
    (hn : 2 ≤ n)
    (hQ : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 1) :
    0 < ∑ i, q i := by
  rw [(unit_deficit_structure q n hn hQ hell).2]
  omega

#print axioms positiveSupport_eq_zero_imp
#print axioms unit_deficit_structure
#print axioms unit_deficit_sum_pos

end JSP000404Research
