import JSP000404Research.SixPointSeparatedSupportTwo
import JSP000404Research.PositiveGapSlots
import Mathlib.Tactic

/-!
# Sharper 14-positive-gap budget in the uncompensated six-centre branch

A top-(n-1) / five-(n-3) six-point profile has at most sixteen
positive quotient positions in general. In the genuinely uncompensated
top-deletion branch, at most three minima can gain after deleting the
top. Every minimum with support three *must* gain. Therefore among
the five minima at most three have support three, and each remaining
minimum has support at most two, so the total is at most

    1 (top) + 3*3 + 2*2 = 14.

No global Boolean-hole payment or geometry exclusion is asserted.
-/

namespace JSP000404Research

open scoped BigOperators

theorem six_point_no_compensation_positive_gap_card_le_fourteen
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3)
    (hNoTop :
      SixPointNoCompensatedTopDeletion
        C (by rw [hcard]; omega) top t n) :
    Fintype.card (GlobalPositiveGapSlot C t) ≤ 14 := by
  classical
  let hcard3 : 3 ≤ Fintype.card V := by omega
  let S : Finset V := Finset.univ.erase top
  let G : Finset V := topDeletionGainMinima C hcard3 top t
  let R : Finset V := S \ G
  let f : V → ℕ := fun i => positiveSupport (centreQuotient (C i) t)
  have hScard : S.card = 5 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ top),
      Finset.card_univ, hcard]
  have hGsub : G ⊆ S := by
    intro i hi
    have hmem :=
      (mem_topDeletionGainMinima_iff C hcard3 top t i).1 hi
    exact Finset.mem_erase.mpr ⟨hmem.1, Finset.mem_univ i⟩
  have hGcard : G.card ≤ 3 := by
    dsimp [G, hcard3]
    exact topDeletionGainMinima_card_le_three_of_no_compensated_top
      C hcard (by omega : 3 ≤ n)
      (sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht).le
      top hTop hMin hNoTop
  have hRcard : R.card = 5 - G.card := by
    dsimp [R]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hGsub,
      hScard]
  have htop : f top ≤ 1 := by
    exact centre_positiveSupport_le_one_of_exponent_n_sub_one
      (C top) (by omega : 4 ≤ n) hdelta0
      (by linarith : delta < 1) ht hTop
  have hminSupport :
      ∀ i : V, i ≠ top → f i ≤ 3 := by
    intro i hi
    exact centre_positiveSupport_le_three_of_exponent_n_sub_three
      (C i) (by omega : 4 ≤ n) hdelta0
      (by linarith : delta < 1) ht (hMin i hi)
  have hsmallRest :
      ∀ i : V, i ∈ R → f i ≤ 2 := by
    intro i hi
    have hiS : i ∈ S := (Finset.mem_sdiff.mp hi).1
    have hiNotG : i ∉ G := (Finset.mem_sdiff.mp hi).2
    have hiTop : i ≠ top := (Finset.mem_erase.mp hiS).1
    by_contra hnot
    have hgt : 2 < f i := by omega
    have h3 : f i = 3 := by
      have hle := hminSupport i hiTop
      omega
    apply hiNotG
    exact support_three_mem_topDeletionGainMinima
      hp hcap C hcard (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      top hTop hiTop (hMin i hiTop) h3
  have hsumG :
      (∑ i ∈ G, f i) ≤ G.card * 3 := by
    calc
      (∑ i ∈ G, f i) ≤ ∑ _i ∈ G, 3 := by
        apply Finset.sum_le_sum
        intro i hi
        exact hminSupport i (Finset.mem_erase.mp (hGsub hi)).1
      _ = G.card * 3 := by simp
  have hsumR :
      (∑ i ∈ R, f i) ≤ R.card * 2 := by
    calc
      (∑ i ∈ R, f i) ≤ ∑ _i ∈ R, 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact hsmallRest i hi
      _ = R.card * 2 := by simp
  have hsplit :
      (∑ i ∈ S, f i) =
        (∑ i ∈ G, f i) + (∑ i ∈ R, f i) := by
    have hsd :
        (∑ i ∈ R, f i) + (∑ i ∈ G, f i) =
          (∑ i ∈ S, f i) := by
      exact Finset.sum_sdiff hGsub
    simpa only [add_comm] using hsd.symm
  rw [globalPositiveGapSlot_card_eq_sum_positiveSupport C t]
  calc
    (∑ i : V, f i) = f top + ∑ i ∈ S, f i := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ top)]
      simp [S, add_comm]
    _ = f top + (∑ i ∈ G, f i) + (∑ i ∈ R, f i) := by
      rw [hsplit]
      omega
    _ ≤ 1 + G.card * 3 + R.card * 2 := by
      omega
    _ ≤ 14 := by
      rw [hRcard]
      omega

#print axioms six_point_no_compensation_positive_gap_card_le_fourteen

end JSP000404Research
