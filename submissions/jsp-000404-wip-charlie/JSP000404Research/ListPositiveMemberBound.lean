import JSP000404Research.SignTransitionBudget
import Mathlib.Tactic

/-!
# A positive quotient pays for the remaining support

For a natural list, every positive entry contributes at least one unit to the
sum.  More precisely, if q is a positive member, then

  q + (positiveSupport - 1) <= total sum.

Thus in a support-three quotient list of total mass n every positive entry is
at most n-2.

This isolates the arithmetic needed to turn any saturated transition in the
deficit-three/support-three branch into a quantitatively large actual angle.
-/

namespace JSP000404Research

theorem listPositiveCount_pos_of_mem_ne_zero
    (qs : List ℕ) {q : ℕ}
    (hqmem : q ∈ qs)
    (hq : q ≠ 0) :
    0 < listPositiveCount qs := by
  induction qs with
  | nil =>
      simp at hqmem
  | cons r rs ih =>
      simp only [List.mem_cons] at hqmem
      by_cases hr : r = 0
      · rcases hqmem with hbad | hmem
        · subst r
          exact False.elim (hq rfl)
        · simp [listPositiveCount, hr]
          exact ih hmem
      · simp [listPositiveCount, hr]

theorem listPositiveCount_le_sum
    (qs : List ℕ) :
    listPositiveCount qs ≤ qs.sum := by
  induction qs with
  | nil =>
      simp [listPositiveCount]
  | cons q qs ih =>
      by_cases hq : q = 0
      · simp [listPositiveCount, hq, ih]
      · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
        simp [listPositiveCount, hq]
        omega

theorem positive_member_add_support_pred_le_sum
    (qs : List ℕ) {q : ℕ}
    (hqmem : q ∈ qs)
    (hq : q ≠ 0) :
    q + (listPositiveCount qs - 1) ≤ qs.sum := by
  induction qs with
  | nil =>
      simp at hqmem
  | cons r rs ih =>
      simp only [List.mem_cons] at hqmem
      by_cases hr : r = 0
      · rcases hqmem with hEq | hmem
        · subst r
          exact False.elim (hq rfl)
        · have hih := ih hmem
          simpa [listPositiveCount, hr] using hih
      · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
        rcases hqmem with hEq | hmem
        · subst r
          have htail := listPositiveCount_le_sum rs
          simp [listPositiveCount, hq]
          omega
        · have hih := ih hmem
          have hcountPos :
              0 < listPositiveCount rs :=
            listPositiveCount_pos_of_mem_ne_zero rs hmem hq
          simp [listPositiveCount, hr]
          omega

theorem positive_member_le_n_sub_two_of_support_three_sum
    (qs : List ℕ) {q n : ℕ}
    (hsupport : listPositiveCount qs = 3)
    (hsum : qs.sum = n)
    (hqmem : q ∈ qs)
    (hq : q ≠ 0) :
    q ≤ n - 2 := by
  have h :=
    positive_member_add_support_pred_le_sum
      qs hqmem hq
  rw [hsupport, hsum] at h
  norm_num at h
  omega

#print axioms listPositiveCount_pos_of_mem_ne_zero
#print axioms listPositiveCount_le_sum
#print axioms positive_member_add_support_pred_le_sum
#print axioms positive_member_le_n_sub_two_of_support_three_sum

end JSP000404Research
