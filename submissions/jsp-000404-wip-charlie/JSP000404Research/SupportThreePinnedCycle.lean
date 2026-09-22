import JSP000404Research.SupportTwoPinnedCycle
import Mathlib.Tactic

/-!
# Three-positive cyclic list pinned at one distinguished ray

If a cyclic quotient list has positive support exactly three and the two
entries adjacent to a distinguished pinned ray are both positive, then the
entire middle block has positive support exactly one.

This is the discrete skeleton of the deficit-three/support-three geometry:
after pinning the sharp ray, the non-sharp path contains one internal positive
edge and all other internal edges are zero.
-/

namespace JSP000404Research

theorem support_three_end_positive_forces_middle_count_one
    (qFirst qLast : ℕ) (mid : List ℕ)
    (hFirst : 1 ≤ qFirst)
    (hLast : 1 ≤ qLast)
    (hsupport :
      listPositiveCount (qFirst :: mid ++ [qLast]) = 3) :
    listPositiveCount mid = 1 := by
  have hF : qFirst ≠ 0 := by omega
  have hL : qLast ≠ 0 := by omega
  rw [listPositiveCount] at hsupport
  simp [hF, listPositiveCount_append, hL] at hsupport
  omega

theorem support_three_middle_count_one_of_end_ne_zero
    (qFirst qLast : ℕ) (mid : List ℕ)
    (hFirst : qFirst ≠ 0)
    (hLast : qLast ≠ 0)
    (hsupport :
      listPositiveCount (qFirst :: mid ++ [qLast]) = 3) :
    listPositiveCount mid = 1 := by
  exact support_three_end_positive_forces_middle_count_one
    qFirst qLast mid
    (Nat.one_le_iff_ne_zero.mpr hFirst)
    (Nat.one_le_iff_ne_zero.mpr hLast)
    hsupport

theorem pinned_support_three_shape_of_end_zero_impossible
    (qFirst qLast : ℕ) (mid : List ℕ)
    (hFirstZero : qFirst = 0 → False)
    (hLastZero : qLast = 0 → False)
    (hsupport :
      listPositiveCount (qFirst :: mid ++ [qLast]) = 3) :
    1 ≤ qFirst ∧
      1 ≤ qLast ∧
      listPositiveCount mid = 1 := by
  have hFirst : 1 ≤ qFirst := by
    by_contra h
    exact hFirstZero (by omega)
  have hLast : 1 ≤ qLast := by
    by_contra h
    exact hLastZero (by omega)
  exact ⟨hFirst, hLast,
    support_three_end_positive_forces_middle_count_one
      qFirst qLast mid hFirst hLast hsupport⟩

#print axioms support_three_end_positive_forces_middle_count_one
#print axioms pinned_support_three_shape_of_end_zero_impossible

end JSP000404Research
