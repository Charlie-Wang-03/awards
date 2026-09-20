import JSP000404Research.AggregateBinarySplit
import JSP000404Research.BalancedBinarySplitHardStop
import Mathlib.Tactic

/-!
# The five-point pointwise-gain hard stop is solved by aggregate splitting

The stable five-point configuration falsifies every pointwise +1 first split.
Nevertheless the weaker child-mass condition succeeds.

Take the table split with left child {0,1} and right child {2,3,4}.  Old child
masses are both 3.  The fixed-t child post masses are respectively 8 and 7.

Hence

  2*3 <= 8,
  2*3 <= 7,

while both child post masses are <= 2^3.  AggregateBinarySplit therefore closes
the parent mass 6 <= 8.

This is an exact arithmetic regression test showing that aggregate recursive
splitting is strictly stronger than pointwise gain splitting.
-/

namespace JSP000404Research

open scoped BigOperators

def aggregateHardStopLeft : Finset (Fin 5) :=
  balancedHardStopLeft 0

def aggregateHardStopRight : Finset (Fin 5) :=
  Finset.univ  aggregateHardStopLeft

def aggregateHardStopPostExp : Fin 5 → ℕ :=
  balancedHardStopPostExp 0

theorem aggregateHardStop_partition :
    Disjoint aggregateHardStopLeft aggregateHardStopRight ∧
      aggregateHardStopLeft ∪ aggregateHardStopRight = Finset.univ := by
  native_decide

theorem aggregateHardStop_old_left_mass :
    (∑ v ∈ aggregateHardStopLeft,
      2 ^ balancedHardStopOldExp v) = 3 := by
  native_decide

theorem aggregateHardStop_old_right_mass :
    (∑ v ∈ aggregateHardStopRight,
      2 ^ balancedHardStopOldExp v) = 3 := by
  native_decide

theorem aggregateHardStop_post_left_mass :
    (∑ v ∈ aggregateHardStopLeft,
      2 ^ aggregateHardStopPostExp v) = 8 := by
  native_decide

theorem aggregateHardStop_post_right_mass :
    (∑ v ∈ aggregateHardStopRight,
      2 ^ aggregateHardStopPostExp v) = 7 := by
  native_decide

theorem aggregateHardStop_left_doubles :
    2 * (∑ v ∈ aggregateHardStopLeft,
      2 ^ balancedHardStopOldExp v)
      ≤
    ∑ v ∈ aggregateHardStopLeft,
      2 ^ aggregateHardStopPostExp v := by
  native_decide

theorem aggregateHardStop_right_doubles :
    2 * (∑ v ∈ aggregateHardStopRight,
      2 ^ balancedHardStopOldExp v)
      ≤
    ∑ v ∈ aggregateHardStopRight,
      2 ^ aggregateHardStopPostExp v := by
  native_decide

/-- The stable pointwise-gain hard stop closes under aggregate binary split. -/
theorem aggregateHardStop_closed :
    (∑ v : Fin 5, 2 ^ balancedHardStopOldExp v) ≤ 2 ^ 3 := by
  rcases aggregateHardStop_partition with ⟨hdisj, hcover⟩
  exact aggregate_binary_split_fintype_capacity
    aggregateHardStopLeft aggregateHardStopRight
    balancedHardStopOldExp
    aggregateHardStopPostExp aggregateHardStopPostExp
    3 hdisj hcover
    aggregateHardStop_left_doubles
    aggregateHardStop_right_doubles
    (by rw [aggregateHardStop_post_left_mass])
    (by rw [aggregateHardStop_post_right_mass]; norm_num)

#print axioms aggregateHardStop_closed

end JSP000404Research
