import JSP000404Research.ZeroCarry
import Mathlib.Tactic

/-!
# Full occupancy and boundary interlacing

For a circular cell partition with k boundaries, let b i be the number of
partition boundaries lying in the i-th radial gap of a fixed vertex.  Assume

  sum_i b i = k.

The number of occupied cells is

  positiveSupport b = k - floorExcess b.

Therefore all k cells are occupied exactly when floorExcess b = 0, equivalently
when no radial gap contains two partition boundaries.

This is the purely finite counting part of the "full vertex iff boundaries
interlace the incident rays" reformulation.  The geometric construction of b
for the rotating standard (n+1)-band partition remains separate.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Zero floor excess is equivalent to every count being at most one. -/
theorem floorExcess_eq_zero_iff_all_le_one
    {I : Type*} [Fintype I]
    (b : I → ℕ) :
    floorExcess b = 0 ↔ ∀ i, b i ≤ 1 := by
  unfold floorExcess
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h i
    have hi := h i (Finset.mem_univ i)
    omega
  · intro h i hi
    have hb := h i
    omega

/-- If the boundary counts sum to k, all k cells are occupied exactly when no
radial gap contains two boundaries. -/
theorem positiveSupport_eq_total_iff_all_le_one
    {I : Type*} [Fintype I]
    (b : I → ℕ) (k : ℕ)
    (hsum : (∑ i, b i) = k) :
    positiveSupport b = k ↔ ∀ i, b i ≤ 1 := by
  have hid := floorExcess_add_positiveSupport b
  rw [hsum] at hid
  constructor
  · intro hsupp
    have hex : floorExcess b = 0 := by omega
    exact (floorExcess_eq_zero_iff_all_le_one b).1 hex
  · intro hle
    have hex : floorExcess b = 0 :=
      (floorExcess_eq_zero_iff_all_le_one b).2 hle
    omega

/-- Equivalent full-occupancy criterion stated directly with floor excess. -/
theorem positiveSupport_eq_total_iff_floorExcess_zero
    {I : Type*} [Fintype I]
    (b : I → ℕ) (k : ℕ)
    (hsum : (∑ i, b i) = k) :
    positiveSupport b = k ↔ floorExcess b = 0 := by
  have hid := floorExcess_add_positiveSupport b
  rw [hsum] at hid
  omega

/-- Any repeated boundary in one radial gap forces at least one missing cell. -/
theorem positiveSupport_lt_total_of_two_le
    {I : Type*} [Fintype I]
    (b : I → ℕ) (k : ℕ)
    (hsum : (∑ i, b i) = k)
    {i : I} (hi : 2 ≤ b i) :
    positiveSupport b < k := by
  have hnot : ¬ ∀ j, b j ≤ 1 := by
    intro hall
    exact (not_le_of_gt hi) (hall i)
  have hiff :=
    positiveSupport_eq_total_iff_all_le_one b k hsum
  have hne : positiveSupport b ≠ k := by
    intro heq
    exact hnot (hiff.1 heq)
  have hle : positiveSupport b ≤ k := by
    have hid := floorExcess_add_positiveSupport b
    rw [hsum] at hid
    omega
  omega

#print axioms floorExcess_eq_zero_iff_all_le_one
#print axioms positiveSupport_eq_total_iff_all_le_one
#print axioms positiveSupport_eq_total_iff_floorExcess_zero
#print axioms positiveSupport_lt_total_of_two_le

end JSP000404Research
