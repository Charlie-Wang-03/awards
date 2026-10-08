import JSP000404Research.ProjectionLossFlipCoordinate
import JSP000404Research.ResidualPairFlipBlocker
import JSP000404Research.TranslatedCompletionCore
import Mathlib.Tactic

/-!
# Translated completion blocks of projected-loss vertices

Fix a retained coordinate c active at a projected-loss vertex v. Translate the
entire retained completion cube Q_v by flipping c.

The translation is an involution, so the translated block has the same
cardinality as Q_v. Since c is active at v, the translated block is disjoint
from Q_v.

If a translated word is captured by some other completion cube Q_w, then c
must be active at w. Otherwise flipping c back would put the original loss
word in Q_w, contradicting the fact that loss completion cubes are disjoint
from every other cube. The blocker bit at c is necessarily the opposite of
the loss vertex bit.

This is the block-level loss analogue of the overlap blocker transition.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem loss_translated_blocker_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V} {c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hc : c ∈ retainedActive C v)
    (hvw : v ≠ w)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v)
    (hw :
      flipBoolWordAt word c ∈ retainedCompletionWords C w) :
    c ∈ retainedActive C w := by
  by_contra hcW
  have hwOrig :
      word ∈ retainedCompletionWords C w :=
    (mem_completion_iff_flip_of_inactive C hcW).1 hw
  have hdisj :=
    projectedLoss_completion_disjoint
      C exponent hexp honeLoss hvLoss hvw
  exact Finset.disjoint_left.mp hdisj hword hwOrig

theorem loss_translated_blocker_bit_opposite
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V} {c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hc : c ∈ retainedActive C v)
    (hvw : v ≠ w)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v)
    (hw :
      flipBoolWordAt word c ∈ retainedCompletionWords C w) :
    retainedBit C w c = !(retainedBit C v c) := by
  have hcW :=
    loss_translated_blocker_active
      C exponent hexp honeLoss hvLoss hc hvw hword hw
  have hvComp :=
    (mem_retainedCompletionWords C v word).1 hword
  have hwComp :=
    (mem_retainedCompletionWords C w
      (flipBoolWordAt word c)).1 hw
  have hvAt := hvComp c hc
  have hwAt := hwComp c hcW
  rw [flipBoolWordAt_at, hvAt] at hwAt
  exact hwAt.symm

theorem loss_translated_blocker_disjoint_original
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V} {c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hc : c ∈ retainedActive C v)
    (hvw : v ≠ w)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v)
    (hw :
      flipBoolWordAt word c ∈ retainedCompletionWords C w) :
    Disjoint
      (retainedCompletionWords C v)
      (retainedCompletionWords C w) := by
  exact projectedLoss_completion_disjoint
    C exponent hexp honeLoss hvLoss hvw

#print axioms translatedCompletionWords_card
#print axioms translatedCompletionWords_disjoint_original_of_active
#print axioms loss_translated_blocker_active
#print axioms loss_translated_blocker_bit_opposite

end OrderedEdgeColoring
end JSP000404Research
