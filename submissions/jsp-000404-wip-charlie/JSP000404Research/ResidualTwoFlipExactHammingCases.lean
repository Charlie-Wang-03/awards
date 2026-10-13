import JSP000404Research.ResidualNetCollisionExactFlipSupport
import Mathlib.Tactic

/-!
# Two distinct double-flip collision sources differ in EXACTLY two or four bits

Each genuine collision diagonal flips exactly two DISTINCT coordinates.
The exact source-disagreement set is the symmetric difference of the
two unordered 2-coordinate colour supports. We certify that this
symmetric difference has cardinality 0, 2 or 4, and 0 is impossible
for two distinct original sink words.

This is an unconditional combinatorial classification of the
global duplicate-image witnesses arising in actual NET collisions,
not a claim that AngleCap excludes the two and four cases.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Two 2-element supports have symmetric difference size only
ZERO, TWO, or FOUR, without assuming anything about their overlap. -/
theorem pair_symmetric_difference_card_zero_two_four
    {α : Type*} [DecidableEq α]
    (a b c d : α) (hab : a ≠ b) (hcd : c ≠ d) :
    ((({a,b} : Finset α) \ ({c,d} : Finset α)) ∪
      (({c,d} : Finset α) \ ({a,b} : Finset α))).card = 0 ∨
    ((({a,b} : Finset α) \ ({c,d} : Finset α)) ∪
      (({c,d} : Finset α) \ ({a,b} : Finset α))).card = 2 ∨
    ((({a,b} : Finset α) \ ({c,d} : Finset α)) ∪
      (({c,d} : Finset α) \ ({a,b} : Finset α))).card = 4 := by
  classical
  let A : Finset α := {a,b}
  let B : Finset α := {c,d}
  let X := A \ B
  let Y := B \ A
  let M := A ∩ B
  have hA : A.card = 2 := by simp [A, hab]
  have hB : B.card = 2 := by simp [B, hcd]
  have hpartA : A = X ∪ M := by
    ext e
    simp only [X, M, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_inter]
    tauto
  have hpartB : B = Y ∪ M := by
    ext e
    simp only [Y, M, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_inter]
    tauto
  have hdisA : Disjoint X M := by
    apply Finset.disjoint_left.mpr
    intro e hx hm
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hm).2
  have hdisB : Disjoint Y M := by
    apply Finset.disjoint_left.mpr
    intro e hy hm
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_inter.mp hm).1
  have hdisXY : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro e hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have hcardA : A.card = X.card + M.card := by
    rw [hpartA, Finset.card_union_of_disjoint hdisA]
  have hcardB : B.card = Y.card + M.card := by
    rw [hpartB, Finset.card_union_of_disjoint hdisB]
  have hcardXY : (X ∪ Y).card = X.card + Y.card :=
    Finset.card_union_of_disjoint hdisXY
  change (X ∪ Y).card = 0 ∨ (X ∪ Y).card = 2 ∨
    (X ∪ Y).card = 4
  omega

/-- For two distinct Boolean source words whose two double-flipped
diagonal targets are equal, the source Hamming distance is
EXACTLY TWO or FOUR, never one or three. -/
theorem two_flip_equal_target_distinct_sources_hamming_two_or_four
    {n : ℕ} (w z : Fin n → Bool)
    (a b c d : Fin n)
    (hab : a ≠ b) (hcd : c ≠ d)
    (heq : flipCompletionWord a (flipCompletionWord b w) =
      flipCompletionWord c (flipCompletionWord d z))
    (hneq : w ≠ z) :
    (Finset.univ.filter (fun e : Fin n => w e ≠ z e)).card = 2 ∨
    (Finset.univ.filter (fun e : Fin n => w e ≠ z e)).card = 4 := by
  classical
  have hsupport :=
    two_flip_equal_target_exact_difference_set
      w z a b c d hab hcd heq
  have hcases :=
    pair_symmetric_difference_card_zero_two_four
      a b c d hab hcd
  have hpositive :
      0 < (Finset.univ.filter (fun e : Fin n => w e ≠ z e)).card := by
    by_contra hn
    have hzero :
        (Finset.univ.filter (fun e : Fin n => w e ≠ z e)).card = 0 := by
      omega
    have hempty :
        Finset.univ.filter (fun e : Fin n => w e ≠ z e) = ∅ :=
      Finset.card_eq_zero.mp hzero
    apply hneq
    funext e
    by_contra hdiff
    have hmem :
        e ∈ Finset.univ.filter (fun i : Fin n => w i ≠ z i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff⟩
    rw [hempty] at hmem
    exact Finset.not_mem_empty e hmem
  rw [← hsupport] at hcases
  omega

#print axioms pair_symmetric_difference_card_zero_two_four
#print axioms two_flip_equal_target_distinct_sources_hamming_two_or_four

end OrderedEdgeColoring
end JSP000404Research
