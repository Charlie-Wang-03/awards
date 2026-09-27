import JSP000404Research.CutBadOrdinaryMismatchShape
import Mathlib.Tactic

/-!
# Ordinary step rigidity for a four-consecutive bad palette

For a cut-sorted five-ray centre, if the first and last occupied old bands
differ by exactly three, then the four ordinary band jumps sum to three.

At every saturation-bad exact n-3 minimum the ordinary band-jump list has
exactly three positive entries.  Hence under this span-three hypothesis each
positive ordinary band jump is exactly one.

Since the ordinary quotient list is pointwise dominated by the band jumps,
every ordinary quotient is then at most one.  Thus every positive ordinary
quotient is exactly one.

This is the arithmetic bridge needed when a support-one bad minimum forces a
four-consecutive old palette and the second bad minimum has the same old
palette.
-/

namespace JSP000404Research

theorem successiveNatDiffsFrom_sum_eq_last_sub_first
    (a : ℕ) (xs : List ℕ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    (successiveNatDiffsFrom a xs).sum =
      xs.getLastD a - a := by
  induction xs generalizing a with
  | nil =>
      simp [successiveNatDiffsFrom]
  | cons b bs ih =>
      have hp := List.pairwise_cons.mp hsorted
      have hab : a ≤ b := hp.1 b (by simp)
      simp only [successiveNatDiffsFrom, List.sum_cons]
      rw [ih b hp.2]
      cases bs with
      | nil =>
          simp
          omega
      | cons c cs =>
          simp only [List.getLastD_cons]
          have hbc :
              b ≤ (c :: cs).getLastD b :=
            head_le_getLastD_of_pairwise b (c :: cs) hp.2
          omega

theorem listPositiveCount_le_sum_self
    (xs : List ℕ) :
    listPositiveCount xs ≤ xs.sum := by
  induction xs with
  | nil => simp [listPositiveCount]
  | cons x xs ih =>
      by_cases hx : x = 0
      · subst x
        simpa [listPositiveCount] using ih
      · simp [listPositiveCount, hx]
        omega

theorem listPositiveCount_erase_add_one_of_mem_pos
    (xs : List ℕ) {b : ℕ}
    (hb : b ∈ xs)
    (hb0 : b ≠ 0) :
    listPositiveCount xs =
      listPositiveCount (xs.erase b) + 1 := by
  induction xs with
  | nil => simp at hb
  | cons x xs ih =>
      simp only [List.mem_cons] at hb
      rcases hb with hxb | hb
      · subst x
        simp [listPositiveCount, hb0]
      · by_cases hxb : x = b
        · subst x
          simp [listPositiveCount, hb0]
        · by_cases hx0 : x = 0
          · subst x
            simp [listPositiveCount, hxb]
            exact ih hb
          · simp [List.erase_cons, hxb,
              listPositiveCount, hx0]
            have hi := ih hb
            omega

theorem list_sum_erase_add_of_mem
    (xs : List ℕ) {b : ℕ}
    (hb : b ∈ xs) :
    (xs.erase b).sum + b = xs.sum := by
  induction xs with
  | nil => simp at hb
  | cons x xs ih =>
      simp only [List.mem_cons] at hb
      rcases hb with hxb | hb
      · subst x
        simp
      · by_cases hxb : x = b
        · subst x
          simp
        · simp [List.erase_cons, hxb]
          rw [ih hb]
          omega

theorem positiveCount_three_sum_three_entries_le_one
    (bs : List ℕ)
    (hpos : listPositiveCount bs = 3)
    (hsum : bs.sum = 3) :
    ∀ b ∈ bs, b ≤ 1 := by
  intro b hb
  by_contra hnot
  have hb2 : 2 ≤ b := by omega
  have hb0 : b ≠ 0 := by omega
  have hcountErase :=
    listPositiveCount_erase_add_one_of_mem_pos bs hb hb0
  have hposErase :
      listPositiveCount (bs.erase b) = 2 := by
    rw [hpos] at hcountErase
    omega
  have hsumEraseLower :
      2 ≤ (bs.erase b).sum := by
    have h :=
      listPositiveCount_le_sum_self (bs.erase b)
    rw [hposErase] at h
    exact h
  have hsumErase :=
    list_sum_erase_add_of_mem bs hb
  rw [hsum] at hsumErase
  omega

theorem forall₂_q_le_b_and_band_le_one_implies_q_le_one
    {qs bs : List ℕ}
    (hdom : List.Forall₂ (· ≤ ·) qs bs)
    (hb1 : ∀ b ∈ bs, b ≤ 1) :
    ∀ q ∈ qs, q ≤ 1 := by
  induction hdom with
  | nil =>
      simp
  | @cons q b qs bs hqb htail ih =>
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hqb.trans (hb1 b (by simp))
      · exact ih
          (fun y hy => hb1 y (by simp [hy]))
          x hx

/-- Under exact span three, every ordinary band jump is zero or one and every
ordinary quotient is zero or one. -/
theorem ordinary_step_shape_of_span_three
    (a : ℝ) (xs : List ℝ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hspan :
      Nat.floor (xs.getLastD a) = Nat.floor a + 3)
    (hdom :
      List.Forall₂ (· ≤ ·)
        ((successiveDiffsFrom a xs).map Nat.floor)
        (successiveNatDiffsFrom (Nat.floor a)
          (xs.map Nat.floor)))
    (hbpos :
      listPositiveCount
        (successiveNatDiffsFrom (Nat.floor a)
          (xs.map Nat.floor)) = 3) :
    (∀ b ∈ successiveNatDiffsFrom (Nat.floor a)
        (xs.map Nat.floor), b ≤ 1)
      ∧
    (∀ q ∈ (successiveDiffsFrom a xs).map Nat.floor,
        q ≤ 1) := by
  have hfloorSorted :
      ((a :: xs).map Nat.floor).Pairwise (· ≤ ·) := by
    exact hsorted.imp
      (fun _ _ hxy => Nat.floor_mono hxy)
  have hnatSorted :
      (Nat.floor a :: xs.map Nat.floor).Pairwise (· ≤ ·) := by
    simpa using hfloorSorted
  have hsum :
      (successiveNatDiffsFrom (Nat.floor a)
        (xs.map Nat.floor)).sum = 3 := by
    rw [successiveNatDiffsFrom_sum_eq_last_sub_first
      (Nat.floor a) (xs.map Nat.floor) hnatSorted]
    have hlast :
        (xs.map Nat.floor).getLastD (Nat.floor a) =
          Nat.floor (xs.getLastD a) := by
      rw [map_getLastD_eq]
    rw [hlast, hspan]
    omega
  have hb1 :=
    positiveCount_three_sum_three_entries_le_one
      _ hbpos hsum
  exact ⟨hb1,
    forall₂_q_le_b_and_band_le_one_implies_q_le_one
      hdom hb1⟩

/-- In the span-three case, every positive ordinary quotient equals one. -/
theorem positive_ordinary_quotient_eq_one_of_span_three
    (a : ℝ) (xs : List ℝ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hspan :
      Nat.floor (xs.getLastD a) = Nat.floor a + 3)
    (hdom :
      List.Forall₂ (· ≤ ·)
        ((successiveDiffsFrom a xs).map Nat.floor)
        (successiveNatDiffsFrom (Nat.floor a)
          (xs.map Nat.floor)))
    (hbpos :
      listPositiveCount
        (successiveNatDiffsFrom (Nat.floor a)
          (xs.map Nat.floor)) = 3)
    {q : ℕ}
    (hqmem :
      q ∈ (successiveDiffsFrom a xs).map Nat.floor)
    (hqpos : q ≠ 0) :
    q = 1 := by
  have hqle :=
    (ordinary_step_shape_of_span_three
      a xs hsorted hspan hdom hbpos).2 q hqmem
  omega

#print axioms successiveNatDiffsFrom_sum_eq_last_sub_first
#print axioms positiveCount_three_sum_three_entries_le_one
#print axioms ordinary_step_shape_of_span_three
#print axioms positive_ordinary_quotient_eq_one_of_span_three

end JSP000404Research
