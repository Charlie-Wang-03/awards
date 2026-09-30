import JSP000404Research.ResidualCompletionAccounting
import JSP000404Research.ResidualTranslatedOverlapHalfCapture
import JSP000404Research.ResidualTranslatedOverlapHalfCaptureTwo
import Mathlib.Tactic

/-!
# Total blocker-incidence budget for a fixed pair displacement

A pair-local one- or two-bit displacement is injective on the source overlap
cube.  Every displaced Boolean word belongs to at most two completion cubes.

Therefore, summing over all blocker vertices w, the number of source words
whose displaced images fall in Q_w is at most twice the source overlap size.

This gives a global incidence budget for one carrier and implies that there can
be at most three blockers capturing strictly more than half of its translated
mass.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem sum_oneFlipCaptured_le_two_mul_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {c : Fin n} :
    (∑ w : V, (oneFlipCapturedSourceWords C u v w c).card)
      ≤
    2 * (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card := by
  classical
  let source :=
    retainedCompletionWords C u ∩ retainedCompletionWords C v
  have hrewrite :
      (∑ w : V, (oneFlipCapturedSourceWords C u v w c).card)
        =
      ∑ word ∈ source,
        (completionFibre C (flipBoolWordAt word c)).card := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro word hword
    rw [show
      ∑ w : V,
          if word ∈ source ∧
            flipBoolWordAt word c ∈ retainedCompletionWords C w
          then 1 else 0
        =
      (completionFibre C (flipBoolWordAt word c)).card by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro w hw
      simp [completionFibre, source]]
    simp only [oneFlipCapturedSourceWords, Finset.card_filter]
  rw [hrewrite]
  calc
    (∑ word ∈ source,
        (completionFibre C (flipBoolWordAt word c)).card)
      ≤ ∑ _word ∈ source, 2 := by
        apply Finset.sum_le_sum
        intro word hword
        exact completionFibre_card_le_two
          C (flipBoolWordAt word c)
    _ = 2 * source.card := by
      simp [Nat.mul_comm]

theorem sum_twoFlipCaptured_le_two_mul_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {c d : Fin n} :
    (∑ w : V, (twoFlipCapturedSourceWords C u v w c d).card)
      ≤
    2 * (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card := by
  classical
  let source :=
    retainedCompletionWords C u ∩ retainedCompletionWords C v
  have hrewrite :
      (∑ w : V, (twoFlipCapturedSourceWords C u v w c d).card)
        =
      ∑ word ∈ source,
        (completionFibre C
          (flipBoolWordAt (flipBoolWordAt word c) d)).card := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro word hword
    rw [show
      ∑ w : V,
          if word ∈ source ∧
            flipBoolWordAt (flipBoolWordAt word c) d ∈
              retainedCompletionWords C w
          then 1 else 0
        =
      (completionFibre C
        (flipBoolWordAt (flipBoolWordAt word c) d)).card by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro w hw
      simp [completionFibre, source]]
    simp only [twoFlipCapturedSourceWords, Finset.card_filter]
  rw [hrewrite]
  calc
    (∑ word ∈ source,
        (completionFibre C
          (flipBoolWordAt (flipBoolWordAt word c) d)).card)
      ≤ ∑ _word ∈ source, 2 := by
        apply Finset.sum_le_sum
        intro word hword
        exact completionFibre_card_le_two
          C (flipBoolWordAt (flipBoolWordAt word c) d)
    _ = 2 * source.card := by
      simp [Nat.mul_comm]

#print axioms sum_oneFlipCaptured_le_two_mul_overlap
#print axioms sum_twoFlipCaptured_le_two_mul_overlap

end OrderedEdgeColoring
end JSP000404Research
