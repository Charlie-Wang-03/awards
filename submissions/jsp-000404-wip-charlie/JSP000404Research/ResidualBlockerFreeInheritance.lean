import JSP000404Research.ResidualPairLocalFlip
import JSP000404Research.ResidualRetainedInactive
import Mathlib.Tactic

/-!
# Free-coordinate inheritance from adjacent blocked words

A completion cube cannot contain two Boolean words which differ in a coordinate
that is active at the carrier.  Therefore, if both x and flip_e(x) lie in Q_w,
the coordinate e must be inactive at w.

This elementary observation is the dimension-preservation mechanism behind
common-inactive hard overlaps: if a translated overlap subcube is captured by
one blocker cube, every internal edge direction of that captured subcube is
forced to remain free at the blocker.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem inactive_of_word_and_flip_mem_completion
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {w : V} {word : Fin n → Bool} {e : Fin n}
    (hword : word ∈ retainedCompletionWords C w)
    (hflip : flipBoolWordAt word e ∈ retainedCompletionWords C w) :
    e ∉ retainedActive C w := by
  intro he
  have hcomp :=
    (mem_retainedCompletionWords C w word).1 hword
  have hcompFlip :=
    (mem_retainedCompletionWords C w
      (flipBoolWordAt word e)).1 hflip
  have h1 := hcomp e he
  have h2 := hcompFlip e he
  rw [flipBoolWordAt_at, h1] at h2
  cases h : retainedBit C w e <;> simp [h] at h2

theorem inactive_of_two_words_differ_only_by_flip
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {w : V} {x y : Fin n → Bool} {e : Fin n}
    (hxy : y = flipBoolWordAt x e)
    (hx : x ∈ retainedCompletionWords C w)
    (hy : y ∈ retainedCompletionWords C w) :
    e ∉ retainedActive C w := by
  subst y
  exact inactive_of_word_and_flip_mem_completion
    C hx hy

theorem inactive_set_of_all_single_flips_mem_completion
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {w : V} {word : Fin n → Bool}
    {S : Finset (Fin n)}
    (hword : word ∈ retainedCompletionWords C w)
    (hflips :
      ∀ e ∈ S,
        flipBoolWordAt word e ∈ retainedCompletionWords C w) :
    S ⊆ retainedInactive C w := by
  intro e he
  apply (mem_retainedInactive C w e).2
  exact inactive_of_word_and_flip_mem_completion
    C hword (hflips e he)

theorem card_active_le_of_all_single_flips_mem_completion
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {w : V} {word : Fin n → Bool}
    {S : Finset (Fin n)}
    (hword : word ∈ retainedCompletionWords C w)
    (hflips :
      ∀ e ∈ S,
        flipBoolWordAt word e ∈ retainedCompletionWords C w) :
    (retainedActive C w).card ≤ n - S.card := by
  have hsub :
      S ⊆ retainedInactive C w :=
    inactive_set_of_all_single_flips_mem_completion
      C hword hflips
  have hcardInactive :
      S.card ≤ (retainedInactive C w).card :=
    Finset.card_le_card hsub
  rw [retainedInactive_card] at hcardInactive
  have hactiveLe :
      (retainedActive C w).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C w)
  omega

#print axioms inactive_of_word_and_flip_mem_completion
#print axioms inactive_set_of_all_single_flips_mem_completion
#print axioms card_active_le_of_all_single_flips_mem_completion

end OrderedEdgeColoring
end JSP000404Research
