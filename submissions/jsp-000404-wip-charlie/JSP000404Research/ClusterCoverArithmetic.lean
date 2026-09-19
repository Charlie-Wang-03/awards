import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Local cluster-cover arithmetic

Suppose a finite family of nonnegative scaled cluster widths has total width
strictly below d+1.  Cover cluster i by floor(width i)+1 unit intervals.

Then every cluster is covered strictly before its allocated integer endpoint,
and the total number of allocated unit intervals is at most

  card(I) + d.

In the Sendov application, card(I)=p is the number of positive quotient gaps
and d=n-Q is the floor defect, so p+d=ell.  Thus a centre of deficit ell admits
a local cover by at most ell unit-width direction intervals.

This file proves only the arithmetic allocation statement; cyclic cluster
extraction and global colour coordination are deliberately separate.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Floors of nonnegative widths whose sum is below d+1 have total at most d. -/
theorem sum_natFloor_le_of_sum_lt_succ
    {I : Type*} [Fintype I]
    (width : I → ℝ) (d : ℕ)
    (hwidth0 : ∀ i, 0 ≤ width i)
    (hsum : (∑ i, width i) < (d : ℝ) + 1) :
    (∑ i, Nat.floor (width i)) ≤ d := by
  classical
  have hpoint :
      ∀ i : I, ((Nat.floor (width i) : ℕ) : ℝ) ≤ width i := by
    intro i
    exact Nat.floor_le (hwidth0 i)
  have hsum_real :
      (∑ i, ((Nat.floor (width i) : ℕ) : ℝ)) ≤
        ∑ i, width i :=
    Finset.sum_le_sum fun i _ => hpoint i
  have hcast :
      (((∑ i, Nat.floor (width i)) : ℕ) : ℝ) =
        ∑ i, ((Nat.floor (width i) : ℕ) : ℝ) := by
    norm_num
  have hlt :
      (((∑ i, Nat.floor (width i)) : ℕ) : ℝ) < (d : ℝ) + 1 := by
    rw [hcast]
    exact hsum_real.trans_lt hsum
  have hnat : (∑ i, Nat.floor (width i)) < d + 1 := by
    exact_mod_cast hlt
  omega

/-- Allocate floor(width)+1 unit intervals to every cluster. -/
noncomputable def clusterUnitCount
    {I : Type*} (width : I → ℝ) (i : I) : ℕ :=
  Nat.floor (width i) + 1

theorem width_lt_clusterUnitCount
    {I : Type*} (width : I → ℝ) (i : I) :
    width i < (clusterUnitCount width i : ℝ) := by
  unfold clusterUnitCount
  rw [Nat.cast_add, Nat.cast_one]
  exact Nat.lt_floor_add_one (width i)

/-- The total number of allocated unit intervals is at most card(I)+d. -/
theorem sum_clusterUnitCount_le
    {I : Type*} [Fintype I]
    (width : I → ℝ) (d : ℕ)
    (hwidth0 : ∀ i, 0 ≤ width i)
    (hsum : (∑ i, width i) < (d : ℝ) + 1) :
    (∑ i, clusterUnitCount width i) ≤ Fintype.card I + d := by
  classical
  have hfloors :=
    sum_natFloor_le_of_sum_lt_succ width d hwidth0 hsum
  unfold clusterUnitCount
  have hsum_eq :
      (∑ i, (Nat.floor (width i) + 1)) =
        (∑ i, Nat.floor (width i)) + Fintype.card I := by
    simp [Finset.sum_add_distrib]
  rw [hsum_eq]
  omega

/-- Combined local allocation certificate. -/
theorem exists_local_unit_allocation
    {I : Type*} [Fintype I]
    (width : I → ℝ) (d : ℕ)
    (hwidth0 : ∀ i, 0 ≤ width i)
    (hsum : (∑ i, width i) < (d : ℝ) + 1) :
    ∃ count : I → ℕ,
      (∀ i, width i < (count i : ℝ)) ∧
      (∑ i, count i) ≤ Fintype.card I + d := by
  refine ⟨clusterUnitCount width, ?_, ?_⟩
  · exact width_lt_clusterUnitCount width
  · exact sum_clusterUnitCount_le width d hwidth0 hsum

#print axioms sum_natFloor_le_of_sum_lt_succ
#print axioms width_lt_clusterUnitCount
#print axioms sum_clusterUnitCount_le
#print axioms exists_local_unit_allocation

end JSP000404Research
