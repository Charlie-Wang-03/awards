import JSP000404Research.SupportTwoDeletion
import Mathlib.Tactic

/-!
# Exponent gain for deleting the pinned ray of a cyclic quotient list

After rotating a cyclic ray list so that the deleted ray is first, its two
adjacent cyclic quotient gaps are the first quotient and the final quotient:

  qFirst :: qmid ++ [qLast].

Deleting the pinned ray merges precisely those two cyclic gaps.  Up to cyclic
rotation, the child quotient list is

  qmid ++ [qLast + qFirst + carry],

where carry is binary but its value is irrelevant for the lower bound.

If qFirst and qLast are positive, the child exponent is at least one larger
than the parent exponent.  This is the list-arithmetic half of the general
sharp-centre deletion bridge.
-/

namespace JSP000404Research

theorem listExponent_append
    (qs₁ qs₂ : List ℕ) :
    listExponent (qs₁ ++ qs₂) =
      listExponent qs₁ + listExponent qs₂ := by
  simp [listExponent, List.map_append]

@[simp] theorem listExponent_singleton
    (q : ℕ) :
    listExponent [q] = excess q := by
  simp [listExponent]

/-- Exact parent exponent for a pinned cyclic list. -/
theorem listExponent_pinned
    (qFirst qLast : ℕ) (qmid : List ℕ) :
    listExponent (qFirst :: qmid ++ [qLast]) =
      excess qFirst + listExponent qmid + excess qLast := by
  simp [listExponent, List.map_append,
    add_assoc, add_left_comm, add_comm]

/-- Exact exponent of the cyclicly merged child, written with the merged
quotient at the end. -/
theorem listExponent_pinned_child
    (qFirst qLast carry : ℕ) (qmid : List ℕ) :
    listExponent (qmid ++ [qLast + qFirst + carry]) =
      listExponent qmid + excess (qLast + qFirst + carry) := by
  simp [listExponent, List.map_append]

/-- Positive quotients on the two sides of the pinned ray force one full
exponent unit of deletion gain. -/
theorem pinned_cyclic_merge_gain_of_end_positive
    (qFirst qLast carry : ℕ)
    (qmid : List ℕ)
    (hFirst : 1 ≤ qFirst)
    (hLast : 1 ≤ qLast) :
    listExponent (qFirst :: qmid ++ [qLast]) + 1 ≤
      listExponent (qmid ++ [qLast + qFirst + carry]) := by
  rw [listExponent_pinned, listExponent_pinned_child]
  have hlocal :=
    excess_merge_gain_of_both_pos
      (a := qLast) (b := qFirst) (c := carry)
      hLast hFirst
  omega

/-- Dyadic weight doubles under the same pinned cyclic merge. -/
theorem pinned_cyclic_merge_doubles_weight
    (qFirst qLast carry : ℕ)
    (qmid : List ℕ)
    (hFirst : 1 ≤ qFirst)
    (hLast : 1 ≤ qLast) :
    2 * 2 ^ listExponent (qFirst :: qmid ++ [qLast]) ≤
      2 ^ listExponent (qmid ++ [qLast + qFirst + carry]) := by
  exact two_mul_pow_le_pow_of_succ_le
    (pinned_cyclic_merge_gain_of_end_positive
      qFirst qLast carry qmid hFirst hLast)

#print axioms pinned_cyclic_merge_gain_of_end_positive
#print axioms pinned_cyclic_merge_doubles_weight

end JSP000404Research
