import JSP000404Research.CyclicActualAngles
import JSP000404Research.SupportTwoNarrowClusters
import JSP000404Research.PinnedCycleRotation
import Mathlib.Tactic

/-!
# Zero-angle blocks around one internal positive quotient

If a quotient/actual-angle list has one positive entry qHidden and every entry
on either side is zero, then the zero-angle mass is exactly the sum of the two
zero-angle blocks.

This file packages the list algebra needed by the pinned support-three centre.
-/

namespace JSP000404Research

theorem listZeroAngleMass_append
    (q₁ q₂ : List ℕ) (A₁ A₂ : List ℝ)
    (hlen : q₁.length = A₁.length) :
    listZeroAngleMass (q₁ ++ q₂) (A₁ ++ A₂) =
      listZeroAngleMass q₁ A₁ +
        listZeroAngleMass q₂ A₂ := by
  induction q₁ generalizing A₁ with
  | nil =>
      have hnil : A₁ = [] :=
        List.length_eq_zero.mp (by simpa using hlen.symm)
      subst A₁
      simp [listZeroAngleMass]
  | cons q qs ih =>
      cases A₁ with
      | nil =>
          simp at hlen
      | cons A As =>
          simp at hlen
          simp only [List.cons_append, listZeroAngleMass]
          rw [ih As hlen]
          ring

theorem listZeroAngleMass_eq_angle_sum_of_all_zero
    (qs : List ℕ) (As : List ℝ)
    (hlen : qs.length = As.length)
    (hzero : ∀ q ∈ qs, q = 0) :
    listZeroAngleMass qs As = As.sum := by
  induction qs generalizing As with
  | nil =>
      have hnil : As = [] :=
        List.length_eq_zero.mp (by simpa using hlen.symm)
      subst As
      simp [listZeroAngleMass]
  | cons q qs ih =>
      cases As with
      | nil =>
          simp at hlen
      | cons A As =>
          simp at hlen
          have hq : q = 0 := hzero q (by simp)
          have htail : ∀ x ∈ qs, x = 0 := by
            intro x hx
            exact hzero x (by simp [hx])
          subst q
          simp [listZeroAngleMass, ih As hlen htail]

theorem listZeroAngleMass_two_zero_blocks
    (left right : List ℕ)
    (leftA rightA : List ℝ)
    (q : ℕ) (A : ℝ)
    (hq0 : q ≠ 0)
    (hlenL : left.length = leftA.length)
    (hlenR : right.length = rightA.length)
    (hleft : ∀ x ∈ left, x = 0)
    (hright : ∀ x ∈ right, x = 0) :
    listZeroAngleMass
        (left ++ q :: right)
        (leftA ++ A :: rightA)
      =
    leftA.sum + rightA.sum := by
  rw [listZeroAngleMass_append
      left (q :: right) leftA (A :: rightA) hlenL]
  rw [listZeroAngleMass_eq_angle_sum_of_all_zero
      left leftA hlenL hleft]
  simp only [listZeroAngleMass, if_neg hq0]
  rw [listZeroAngleMass_eq_angle_sum_of_all_zero
      right rightA hlenR hright]
  ring

theorem listZeroAngleMass_positive_ends_eq_middle
    (qFirst qLast : ℕ)
    (mid : List ℕ)
    (AFirst ALast : ℝ)
    (Amid : List ℝ)
    (hFirst : qFirst ≠ 0)
    (hLast : qLast ≠ 0)
    (hlen : mid.length = Amid.length) :
    listZeroAngleMass
        (qFirst :: mid ++ [qLast])
        (AFirst :: Amid ++ [ALast])
      =
    listZeroAngleMass mid Amid := by
  simp only [listZeroAngleMass, if_neg hFirst, zero_add]
  rw [listZeroAngleMass_append
      mid [qLast] Amid [ALast] hlen]
  simp [listZeroAngleMass, hLast]

/-- A support-one middle block splits at its unique positive quotient into two
zero quotient blocks, aligned with the corresponding actual-angle blocks. -/
theorem exists_two_zero_angle_blocks_of_positiveCount_one
    (mid : List ℕ) (Amid : List ℝ)
    (hcount : listPositiveCount mid = 1)
    (hlen : mid.length = Amid.length) :
    ∃ left right : List ℕ,
      ∃ qHidden : ℕ,
      ∃ leftA rightA : List ℝ,
      ∃ AHidden : ℝ,
        mid = left ++ qHidden :: right ∧
        Amid = leftA ++ AHidden :: rightA ∧
        qHidden ≠ 0 ∧
        left.length = leftA.length ∧
        right.length = rightA.length ∧
        (∀ q ∈ left, q = 0) ∧
        (∀ q ∈ right, q = 0) ∧
        listZeroAngleMass mid Amid =
          leftA.sum + rightA.sum := by
  have hsumPos :
      0 < mid.sum :=
    list_sum_pos_of_positiveCount_pos mid (by omega)
  have hsumMem :
      mid.sum ∈ mid :=
    list_sum_mem_of_positiveCount_one
      mid hcount hsumPos
  obtain ⟨left, right, hsplit, hleft, hright⟩ :=
    split_unique_positive_of_count_one
      mid mid.sum (by omega) hcount hsumMem
  have hsplitLen :
      (left ++ mid.sum :: right).length = Amid.length := by
    rw [← hsplit, hlen]
  obtain ⟨leftA, AHidden, rightA, hsplitA, hleftLen⟩ :=
    companion_decomposition_at_prefix
      left mid.sum right Amid hsplitLen
  have hrightLen :
      right.length = rightA.length := by
    have hfull := congrArg List.length hsplitA
    simp at hfull
    rw [hleftLen] at hfull
    omega
  have hmass :
      listZeroAngleMass mid Amid =
        leftA.sum + rightA.sum := by
    rw [hsplit, hsplitA]
    exact listZeroAngleMass_two_zero_blocks
      left right leftA rightA mid.sum AHidden
      (by omega) hleftLen.symm hrightLen
      hleft hright
  exact ⟨left, right, mid.sum,
    leftA, rightA, AHidden,
    hsplit, hsplitA, by omega,
    hleftLen.symm, hrightLen,
    hleft, hright, hmass⟩

#print axioms listZeroAngleMass_append
#print axioms listZeroAngleMass_two_zero_blocks
#print axioms listZeroAngleMass_positive_ends_eq_middle
#print axioms exists_two_zero_angle_blocks_of_positiveCount_one

end JSP000404Research
