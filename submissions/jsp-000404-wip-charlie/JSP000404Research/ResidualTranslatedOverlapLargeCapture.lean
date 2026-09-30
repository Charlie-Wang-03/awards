import JSP000404Research.ResidualTranslatedOverlapHalfCapture
import JSP000404Research.ResidualTranslatedOverlapHalfCaptureTwo
import Mathlib.Tactic

/-!
# Large capture forces full free-dimension inheritance

The half-capture lemmas have a useful contrapositive.

If one blocker cube captures strictly more than half of a translated overlap
cube, then no common-inactive coordinate of the source pair may be active at
that blocker. Hence the blocker inherits the entire common-inactive palette.

Therefore every "large" cross-carrier collision preserves at least the full
source overlap dimension. Small collisions lose at least a factor two and are
suited to Kraft/geometric accounting; large collisions are dimension-rigid.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem commonInactive_subset_blockerInactive_of_large_oneFlip_capture
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    (hc : c ∈ retainedActive C u)
    (hlarge :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        <
      2 * (oneFlipCapturedSourceWords C u v w c).card) :
    commonInactiveRetained C u v ⊆ retainedInactive C w := by
  intro e he
  apply (mem_retainedInactive C w e).2
  intro heW
  have hhalf :=
    two_mul_oneFlipCaptured_le_overlap_of_commonInactive_active
      C he hc heW
  omega

theorem commonInactive_subset_blockerInactive_of_large_twoFlip_capture
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c d : Fin n}
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v)
    (hlarge :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        <
      2 * (twoFlipCapturedSourceWords C u v w c d).card) :
    commonInactiveRetained C u v ⊆ retainedInactive C w := by
  intro e he
  apply (mem_retainedInactive C w e).2
  intro heW
  have hhalf :=
    two_mul_twoFlipCaptured_le_overlap_of_commonInactive_active
      C he hc hd heW
  omega

theorem commonInactive_card_le_blockerInactive_of_large_oneFlip_capture
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    (hc : c ∈ retainedActive C u)
    (hlarge :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        <
      2 * (oneFlipCapturedSourceWords C u v w c).card) :
    (commonInactiveRetained C u v).card ≤
      (retainedInactive C w).card := by
  exact Finset.card_le_card
    (commonInactive_subset_blockerInactive_of_large_oneFlip_capture
      C hc hlarge)

theorem commonInactive_card_le_blockerInactive_of_large_twoFlip_capture
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c d : Fin n}
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v)
    (hlarge :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        <
      2 * (twoFlipCapturedSourceWords C u v w c d).card) :
    (commonInactiveRetained C u v).card ≤
      (retainedInactive C w).card := by
  exact Finset.card_le_card
    (commonInactive_subset_blockerInactive_of_large_twoFlip_capture
      C hc hd hlarge)

theorem blockerActive_card_le_of_large_oneFlip_capture
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    (hc : c ∈ retainedActive C u)
    (hlarge :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        <
      2 * (oneFlipCapturedSourceWords C u v w c).card) :
    (retainedActive C w).card ≤
      n - (commonInactiveRetained C u v).card := by
  have hfree :=
    commonInactive_card_le_blockerInactive_of_large_oneFlip_capture
      C hc hlarge
  rw [retainedInactive_card] at hfree
  have hact :
      (retainedActive C w).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C w)
  omega

theorem blockerActive_card_le_of_large_twoFlip_capture
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c d : Fin n}
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v)
    (hlarge :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        <
      2 * (twoFlipCapturedSourceWords C u v w c d).card) :
    (retainedActive C w).card ≤
      n - (commonInactiveRetained C u v).card := by
  have hfree :=
    commonInactive_card_le_blockerInactive_of_large_twoFlip_capture
      C hc hd hlarge
  rw [retainedInactive_card] at hfree
  have hact :
      (retainedActive C w).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C w)
  omega

#print axioms commonInactive_subset_blockerInactive_of_large_oneFlip_capture
#print axioms commonInactive_subset_blockerInactive_of_large_twoFlip_capture
#print axioms blockerActive_card_le_of_large_oneFlip_capture
#print axioms blockerActive_card_le_of_large_twoFlip_capture

end OrderedEdgeColoring
end JSP000404Research
