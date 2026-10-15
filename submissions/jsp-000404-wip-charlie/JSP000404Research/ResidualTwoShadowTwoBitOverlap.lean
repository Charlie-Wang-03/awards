import JSP000404Research.ResidualTwoShadowParityGate
import Mathlib.Tactic

/-!
# Exact one-coordinate intersection in a two-bit shared-shadow conflict

When a single actual SOFT word is Hamming distance two from two
different NET diagonals separated by exactly TWO coordinates, its
two size-two flip sets intersect in EXACTLY ONE coordinate.

Paired with ResidualTwoShadowFourBitDisjoint, this gives an exhaustive
local support intersection classification:
- distance two: flip supports share one coordinate;
- distance four: flip supports are disjoint.

Neither case supplies an independent TRUE hole or unreserved surplus.
-/

namespace JSP000404Research

theorem shared_two_shadow_two_bit_flip_intersection_card_one
    {n : ℕ} (s d e : Fin n → Bool)
    (hsd : (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)
    (hse : (Finset.univ.filter (fun i : Fin n => s i ≠ e i)).card = 2)
    (hde : (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card = 2) :
    ((Finset.univ.filter (fun i : Fin n => s i ≠ d i)) ∩
      (Finset.univ.filter (fun i : Fin n => s i ≠ e i))).card = 1 := by
  classical
  let A : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => s i ≠ d i)
  let B : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => s i ≠ e i)
  let T : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => d i ≠ e i)
  have hT : T = (A \ B) ∪ (B \ A) := by
    ext i
    cases hs : s i <;> cases hd : d i <;> cases he : e i <;>
      simp [T, A, B, hs, hd, he]
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
    calc
      A.card = ((A \ B) ∪ (A ∩ B)).card := congrArg Finset.card hpartA
      _ = (A \ B).card + (A ∩ B).card :=
        Finset.card_union_of_disjoint hdisA
  have hcountB : B.card = (B \ A).card + (A ∩ B).card := by
    calc
      B.card = ((B \ A) ∪ (A ∩ B)).card := congrArg Finset.card hpartB
      _ = (B \ A).card + (A ∩ B).card :=
        Finset.card_union_of_disjoint hdisB
  have hcountT : T.card = (A \ B).card + (B \ A).card := by
    calc
      T.card = ((A \ B) ∪ (B \ A)).card := congrArg Finset.card hT
      _ = (A \ B).card + (B \ A).card :=
        Finset.card_union_of_disjoint hdisT
  have hA : A.card = 2 := hsd
  have hB : B.card = 2 := hse
  have hTc : T.card = 2 := hde
  change (A ∩ B).card = 1
  omega

/-- A shared Hamming-two flip coordinate cannot itself be a coordinate
where the two Boolean targets differ: among two Boolean values a third
distinct value is impossible. In the distance-two case the previously
proved one-coordinate overlap is therefore an *outside* pivot. -/
theorem shared_two_shadow_common_flip_outside_target_difference
    {n : ℕ} (s d e : Fin n → Bool) :
    Disjoint
      ((Finset.univ.filter (fun i : Fin n => s i ≠ d i)) ∩
        (Finset.univ.filter (fun i : Fin n => s i ≠ e i)))
      (Finset.univ.filter (fun i : Fin n => d i ≠ e i)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hde
  have hsd : s i ≠ d i := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2
  have hse : s i ≠ e i := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
  have hne : d i ≠ e i := (Finset.mem_filter.mp hde).2
  cases hs : s i <;> cases hd : d i <;> cases he : e i <;>
    simp_all

/-- Every distance-two common shadow determines a UNIQUE third-colour
pivot: both flipped supports contain precisely the same one coordinate
outside the pairwise target-difference support. -/
theorem shared_two_shadow_two_bit_unique_outside_pivot
    {n : ℕ} (s d e : Fin n → Bool)
    (hsd : (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)
    (hse : (Finset.univ.filter (fun i : Fin n => s i ≠ e i)).card = 2)
    (hde : (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card = 2) :
    ∃! i : Fin n, s i ≠ d i ∧ s i ≠ e i ∧ d i = e i := by
  classical
  let A : Finset (Fin n) :=
    (Finset.univ.filter (fun i : Fin n => s i ≠ d i)) ∩
      (Finset.univ.filter (fun i : Fin n => s i ≠ e i))
  have hcard : A.card = 1 := by
    exact shared_two_shadow_two_bit_flip_intersection_card_one
      s d e hsd hse hde
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have hmem : i ∈ A := by rw [hi]; simp
  have hsmem : s i ≠ d i ∧ s i ≠ e i := by
    have hparts := Finset.mem_inter.mp hmem
    exact ⟨(Finset.mem_filter.mp hparts.1).2,
      (Finset.mem_filter.mp hparts.2).2⟩
  have houtside : d i = e i := by
    by_contra hne
    have hdisj :=
      shared_two_shadow_common_flip_outside_target_difference s d e
    have hneMem : i ∈ Finset.univ.filter (fun i : Fin n => d i ≠ e i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    exact (Finset.disjoint_left.mp hdisj) hmem hneMem
  refine ⟨i, ⟨hsmem.1, hsmem.2, houtside⟩, ?_⟩
  intro j hj
  have hjmem : j ∈ A := by
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.2.1⟩⟩
  rw [hi] at hjmem
  simpa using hjmem

#print axioms shared_two_shadow_common_flip_outside_target_difference
#print axioms shared_two_shadow_two_bit_unique_outside_pivot

#print axioms shared_two_shadow_two_bit_flip_intersection_card_one

end JSP000404Research
