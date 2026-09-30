import JSP000404Research.ResidualTranslatedOverlapHalfCapture
import JSP000404Research.ResidualTranslatedOverlapHalfCaptureTwo
import Mathlib.Tactic

/-!
# Full-free inheritance or half capture

For a blocker of a translated overlap cube there is a sharp dichotomy.

Either every common-inactive source direction remains inactive at the blocker,
or some such direction is active there.  In the latter case the corresponding
edge pairing gives a factor-two capture loss.

This packages the local collision geometry in the exact form needed for a
Kraft/branching argument.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_blocker_fullFree_or_halfCapture
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    (hc : c ∈ retainedActive C u) :
    commonInactiveRetained C u v ⊆ retainedInactive C w
    ∨
    2 * (oneFlipCapturedSourceWords C u v w c).card ≤
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card := by
  classical
  by_cases hsub :
      commonInactiveRetained C u v ⊆ retainedInactive C w
  · exact Or.inl hsub
  · right
    push_neg at hsub
    obtain ⟨e,heCommon,heNotInactive⟩ := hsub
    have heW : e ∈ retainedActive C w := by
      by_contra heInactive
      exact heNotInactive
        ((mem_retainedInactive C w e).2 heInactive)
    exact
      two_mul_oneFlipCaptured_le_overlap_of_commonInactive_active
        C heCommon hc heW

theorem twoFlip_blocker_fullFree_or_halfCapture
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c d : Fin n}
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v) :
    commonInactiveRetained C u v ⊆ retainedInactive C w
    ∨
    2 * (twoFlipCapturedSourceWords C u v w c d).card ≤
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card := by
  classical
  by_cases hsub :
      commonInactiveRetained C u v ⊆ retainedInactive C w
  · exact Or.inl hsub
  · right
    push_neg at hsub
    obtain ⟨e,heCommon,heNotInactive⟩ := hsub
    have heW : e ∈ retainedActive C w := by
      by_contra heInactive
      exact heNotInactive
        ((mem_retainedInactive C w e).2 heInactive)
    exact
      two_mul_twoFlipCaptured_le_overlap_of_commonInactive_active
        C heCommon hc hd heW

theorem commonInactive_card_le_blocker_free_of_fullFree
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V}
    (hsub :
      commonInactiveRetained C u v ⊆ retainedInactive C w) :
    (commonInactiveRetained C u v).card ≤ projectedFree C w := by
  have hcard :=
    Finset.card_le_card hsub
  rw [retainedInactive_card] at hcard
  exact hcard

#print axioms oneFlip_blocker_fullFree_or_halfCapture
#print axioms twoFlip_blocker_fullFree_or_halfCapture
#print axioms commonInactive_card_le_blocker_free_of_fullFree

end OrderedEdgeColoring
end JSP000404Research
