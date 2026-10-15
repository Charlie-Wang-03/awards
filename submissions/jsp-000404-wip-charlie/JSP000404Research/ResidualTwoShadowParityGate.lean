import JSP000404Research.ResidualTwoShadowTargetSeparation
import Mathlib.Tactic

/-!
# Parity sharpening for cross-target Hamming-two SOFT-shadow reuse

For a Boolean word s at Hamming distance exactly two from two distinct
targets d,e, their mutual distance is EXACTLY two or four (never 1 or 3).
The proof partitions each size-two difference support into the shared
support and the two disjoint differences.

In ambient Boolean dimension at most three, shared shadow reuse can
therefore occur only between distance-two targets, never a four-bit pair.
This is a necessary local obstruction, not a proof that actual NET
targets satisfy any separation from the planar AngleCap hypothesis.
-/

namespace JSP000404Research

theorem distinct_targets_of_shared_two_shadow_hamming_two_or_four
    {n : ℕ} (s d e : Fin n → Bool)
    (hd : (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)
    (he : (Finset.univ.filter (fun i : Fin n => s i ≠ e i)).card = 2)
    (hne : d ≠ e) :
    (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card = 2 ∨
      (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card = 4 := by
  classical
  let A : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => s i ≠ d i)
  let B : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => s i ≠ e i)
  let T : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => d i ≠ e i)
  have hA : A.card = 2 := hd
  have hB : B.card = 2 := he
  have hT : T = (A \ B) ∪ (B \ A) := by
    ext i
    cases hs : s i <;> cases hdi : d i <;> cases hei : e i <;>
      simp [T, A, B, hs, hdi, hei]
  have hpartA : A = (A \ B) ∪ (A ∩ B) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hpartB : B = (B \ A) ∪ (A ∩ B) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdisA : Disjoint (A \ B) (A ∩ B) := by
    apply Finset.disjoint_left.mpr
    intro i hi hboth
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hboth).2
  have hdisB : Disjoint (B \ A) (A ∩ B) := by
    apply Finset.disjoint_left.mpr
    intro i hi hboth
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hboth).1
  have hdisT : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hcountA : A.card = (A \ B).card + (A ∩ B).card := by
    rw [hpartA, Finset.card_union_of_disjoint hdisA]
  have hcountB : B.card = (B \ A).card + (A ∩ B).card := by
    rw [hpartB, Finset.card_union_of_disjoint hdisB]
  have hcountT : T.card = (A \ B).card + (B \ A).card := by
    rw [hT, Finset.card_union_of_disjoint hdisT]
  have hpositive : 0 < T.card := by
    by_contra hnot
    have hz : T.card = 0 := by omega
    have hempty : T = ∅ := Finset.card_eq_zero.mp hz
    apply hne
    funext i
    by_contra hdiff
    have hi : i ∈ T :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff⟩
    simp [hempty] at hi
  change T.card = 2 ∨ T.card = 4
  omega

/-- The four-bit branch is absent for ambient dimension at most three. -/
theorem shared_two_shadow_three_bit_targets_distance_two
    {n : ℕ} (hn : n ≤ 3) (s d e : Fin n → Bool)
    (hd : (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)
    (he : (Finset.univ.filter (fun i : Fin n => s i ≠ e i)).card = 2)
    (hne : d ≠ e) :
    (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card = 2 := by
  classical
  have hcases :=
    distinct_targets_of_shared_two_shadow_hamming_two_or_four
      s d e hd he hne
  have hbound :
      (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card ≤ n := by
    simpa using
      (Finset.card_le_card
        (Finset.filter_subset
          (fun i : Fin n => d i ≠ e i) Finset.univ))
  rcases hcases with htwo | hfour
  · exact htwo
  · omega

#print axioms distinct_targets_of_shared_two_shadow_hamming_two_or_four
#print axioms shared_two_shadow_three_bit_targets_distance_two

end JSP000404Research
