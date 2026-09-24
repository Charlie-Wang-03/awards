
import JSP000404Research.PinnedCyclicDeletionGain
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Quotient exponent is invariant under cyclic gap rotation

Changing the cut on a projective circle does not alter its cyclic geometry; it
only rotates the cyclic gap list.

This file isolates the arithmetic backend:

* mapping a floor quotient over a rotated gap list rotates the quotient list;
* list sums are invariant under rotation;
* hence listExponent is invariant under rotation.

Therefore every later geometric change-of-cut theorem only has to identify the
new gap list as a List.rotate of the old one.
-/

namespace JSP000404Research

theorem listNatSum_rotate
    (xs : List ℕ) (r : ℕ) :
    (xs.rotate r).sum = xs.sum := by
  let m := r % xs.length
  rw [List.rotate_eq_drop_append_take_mod,
      List.sum_append]
  calc
    (xs.drop m).sum + (xs.take m).sum
        =
      (xs.take m).sum + (xs.drop m).sum := by
        omega
    _ = xs.sum := by
      rw [← List.sum_append,
          List.take_append_drop]

theorem quotientList_rotate
    (t : ℝ) (gaps : List ℝ) (r : ℕ) :
    quotientList t (gaps.rotate r) =
      (quotientList t gaps).rotate r := by
  simp [quotientList, List.map_rotate]

theorem listExponent_rotate
    (qs : List ℕ) (r : ℕ) :
    listExponent (qs.rotate r) =
      listExponent qs := by
  unfold listExponent
  rw [List.map_rotate, listNatSum_rotate]

theorem listExponent_quotientList_rotate
    (t : ℝ) (gaps : List ℝ) (r : ℕ) :
    listExponent (quotientList t (gaps.rotate r)) =
      listExponent (quotientList t gaps) := by
  rw [quotientList_rotate, listExponent_rotate]

/-- Geometric adapter: equality up to a cyclic gap rotation is enough to
identify the quotient-list exponent. -/
theorem listExponent_quotientList_eq_of_gap_rotate
    (t : ℝ) (gaps gaps' : List ℝ) (r : ℕ)
    (hrot : gaps' = gaps.rotate r) :
    listExponent (quotientList t gaps') =
      listExponent (quotientList t gaps) := by
  rw [hrot]
  exact listExponent_quotientList_rotate t gaps r

#print axioms listNatSum_rotate
#print axioms quotientList_rotate
#print axioms listExponent_rotate
#print axioms listExponent_quotientList_rotate
#print axioms listExponent_quotientList_eq_of_gap_rotate

end JSP000404Research
