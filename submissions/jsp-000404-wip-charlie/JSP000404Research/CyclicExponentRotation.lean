
import JSP000404Research.PinnedCyclicDeletionGain
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Cyclic rotation invariance of quotient-list exponent

The Sendov quotient-list exponent is a commutative sum of the pointwise
excess function.  Hence it is invariant under cyclic rotation.

This trivial-looking fact is the final arithmetic step needed when two
projective angle cuts produce quotient-gap lists that differ only by rotation.
-/

namespace JSP000404Research

theorem listExponent_rotate
    (qs : List ℕ) (k : ℕ) :
    listExponent (qs.rotate k) = listExponent qs := by
  unfold listExponent
  have hp :
      (qs.rotate k).map excess ~ qs.map excess :=
    (List.rotate_perm qs k).map excess
  exact hp.sum_eq

theorem dyadic_listExponent_rotate
    (qs : List ℕ) (k : ℕ) :
    2 ^ listExponent (qs.rotate k) =
      2 ^ listExponent qs := by
  rw [listExponent_rotate]

#print axioms listExponent_rotate
#print axioms dyadic_listExponent_rotate

end JSP000404Research
