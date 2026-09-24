
import JSP000404Research.CentreExponent
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Quotient and exponent invariance under cyclic rotation

The Sendov centre exponent is a cyclic invariant of the projective gap list.

Both quotientList and listExponent are pointwise/list-sum constructions, so
they commute with List.rotate.  Consequently any two concrete gap lists which
differ only by cyclic rotation have identical quotient exponent.

This is the exact arithmetic interface needed after changing the projective
angular cut: the geometry only has to prove that the new cyclic gap list is a
rotation of the canonical one.
-/

namespace JSP000404Research

theorem list_map_rotate
    {α β : Type*}
    (f : α → β) (xs : List α) (k : ℕ) :
    (xs.rotate k).map f =
      (xs.map f).rotate k := by
  simpa using List.map_rotate f xs k

theorem quotientList_rotate
    (t : ℝ) (gaps : List ℝ) (k : ℕ) :
    quotientList t (gaps.rotate k) =
      (quotientList t gaps).rotate k := by
  unfold quotientList
  exact list_map_rotate
    (fun g : ℝ => Nat.floor (t * g))
    gaps k

theorem list_sum_rotate
    {α : Type*} [AddCommMonoid α]
    (xs : List α) (k : ℕ) :
    (xs.rotate k).sum = xs.sum := by
  exact List.sum_rotate xs k

theorem listExponent_rotate
    (qs : List ℕ) (k : ℕ) :
    listExponent (qs.rotate k) =
      listExponent qs := by
  unfold listExponent
  rw [list_map_rotate, list_sum_rotate]

theorem listExponent_quotientList_rotate
    (t : ℝ) (gaps : List ℝ) (k : ℕ) :
    listExponent (quotientList t (gaps.rotate k)) =
      listExponent (quotientList t gaps) := by
  rw [quotientList_rotate, listExponent_rotate]

/-- Equality up to one explicit cyclic rotation preserves the quotient
exponent. -/
theorem listExponent_quotientList_eq_of_eq_rotate
    (t : ℝ) (gaps₁ gaps₂ : List ℝ) (k : ℕ)
    (hrot : gaps₂ = gaps₁.rotate k) :
    listExponent (quotientList t gaps₂) =
      listExponent (quotientList t gaps₁) := by
  rw [hrot]
  exact listExponent_quotientList_rotate t gaps₁ k

#print axioms quotientList_rotate
#print axioms listExponent_rotate
#print axioms listExponent_quotientList_rotate
#print axioms listExponent_quotientList_eq_of_eq_rotate

end JSP000404Research
