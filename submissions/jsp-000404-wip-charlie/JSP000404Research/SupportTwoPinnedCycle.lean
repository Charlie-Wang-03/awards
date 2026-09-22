import JSP000404Research.SignTransitionBudget
import Mathlib.Tactic

/-!
# Two-positive cyclic list pinned at one distinguished ray

Rotate a cyclic ray list so that a distinguished ray is first.  Its two
adjacent cyclic gaps are then the first ordinary gap and the final wrap gap.

If a quotient list has positive support exactly two and both of those adjacent
entries are positive, every interior quotient entry is zero.

This is the finite combinatorial skeleton behind the arbitrary-cardinality
support-two geometry around a sharp centre: once the two gaps adjacent to the
sharp ray are forced positive, all remaining rays form one zero-gap block.
-/

namespace JSP000404Research

theorem positiveCount_cons_eq
    (q : ℕ) (qs : List ℕ) :
    listPositiveCount (q :: qs) =
      (if q = 0 then 0 else 1) + listPositiveCount qs := by
  rfl

theorem positiveCount_eq_zero_iff_all_zero
    (qs : List ℕ) :
    listPositiveCount qs = 0 ↔ ∀ q ∈ qs, q = 0 := by
  induction qs with
  | nil =>
      simp [listPositiveCount]
  | cons q qs ih =>
      by_cases hq : q = 0
      · subst q
        simp [listPositiveCount, ih]
      · constructor
        · intro h
          simp [listPositiveCount, hq] at h
        · intro h
          have := h q (by simp)
          exact False.elim (hq this)

theorem interior_zero_of_support_two_end_positive
    (qFirst : ℕ) (mid : List ℕ) (qLast : ℕ)
    (hFirst : qFirst ≠ 0)
    (hLast : qLast ≠ 0)
    (hsupport :
      listPositiveCount (qFirst :: (mid ++ [qLast])) = 2) :
    ∀ q ∈ mid, q = 0 := by
  have hcount :
      listPositiveCount mid = 0 := by
    rw [listPositiveCount] at hsupport
    simp [hFirst, listPositiveCount_append, hLast] at hsupport
    omega
  exact (positiveCount_eq_zero_iff_all_zero mid).1 hcount

/-- Equivalent decomposition form, useful after rotating the ray cycle to a
distinguished first ray. -/
theorem support_two_end_positive_forces_zero_middle
    (qFirst qLast : ℕ) (mid : List ℕ)
    (hFirst : 1 ≤ qFirst)
    (hLast : 1 ≤ qLast)
    (hsupport :
      listPositiveCount (qFirst :: mid ++ [qLast]) = 2) :
    listPositiveCount mid = 0 := by
  have hF : qFirst ≠ 0 := by omega
  have hL : qLast ≠ 0 := by omega
  have h :=
    interior_zero_of_support_two_end_positive
      qFirst mid qLast hF hL
      (by simpa [List.cons_append] using hsupport)
  exact (positiveCount_eq_zero_iff_all_zero mid).2 h

/-- Any two displayed middle entries are therefore zero. -/
theorem two_middle_entries_zero_of_support_two_end_positive
    (qFirst qLast : ℕ) (mid : List ℕ)
    (hFirst : 1 ≤ qFirst)
    (hLast : 1 ≤ qLast)
    (hsupport :
      listPositiveCount (qFirst :: mid ++ [qLast]) = 2)
    {a b : ℕ}
    (ha : a ∈ mid) (hb : b ∈ mid) :
    a = 0 ∧ b = 0 := by
  have hz :=
    support_two_end_positive_forces_zero_middle
      qFirst qLast mid hFirst hLast hsupport
  have hall :=
    (positiveCount_eq_zero_iff_all_zero mid).1 hz
  exact ⟨hall a ha, hall b hb⟩

#print axioms positiveCount_eq_zero_iff_all_zero
#print axioms interior_zero_of_support_two_end_positive
#print axioms support_two_end_positive_forces_zero_middle

end JSP000404Research
