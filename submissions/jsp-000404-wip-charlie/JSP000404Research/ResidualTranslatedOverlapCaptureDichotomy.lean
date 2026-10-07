import JSP000404Research.ResidualTranslatedOverlapHalfCapture
import JSP000404Research.ResidualTranslatedOverlapHalfCaptureTwo
import JSP000404Research.ResidualTranslatedOverlapLargeCapture
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
    obtain ⟨e,heCommon,heNotInactive⟩ :=
      Finset.not_subset.1 hsub
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
    obtain ⟨e,heCommon,heNotInactive⟩ :=
      Finset.not_subset.1 hsub
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


theorem overlap_card_le_blockerCompletion_of_fullFree
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V}
    (hsub :
      commonInactiveRetained C u v ⊆ retainedInactive C w) :
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card ≤
      (retainedCompletionWords C w).card := by
  classical
  by_cases hempty :
      retainedCompletionWords C u ∩
        retainedCompletionWords C v = ∅
  · rw [hempty]
    simp
  · have hnonempty :
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨base,hbase⟩ := hnonempty
    have hbaseParts := Finset.mem_inter.mp hbase
    have hcard :=
      Finset.card_le_card hsub
    have hpow :=
      Nat.pow_le_pow_right
        (by norm_num : 0 < 2) hcard
    rw [retainedCompletionWords_inter_card_eq_pow_commonInactive
          C hbaseParts.1 hbaseParts.2,
        retainedCompletionWords_card]
    rw [retainedInactive_card] at hpow
    exact hpow

theorem oneFlip_blocker_halfCapture_or_fullCapacity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    (hc : c ∈ retainedActive C u) :
    2 * (oneFlipCapturedSourceWords C u v w c).card ≤
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card
    ∨
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card ≤
        (retainedCompletionWords C w).card := by
  rcases oneFlip_blocker_fullFree_or_halfCapture
      C hc with hfree | hhalf
  · exact Or.inr
      (overlap_card_le_blockerCompletion_of_fullFree
        C hfree)
  · exact Or.inl hhalf

theorem twoFlip_blocker_halfCapture_or_fullCapacity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c d : Fin n}
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v) :
    2 * (twoFlipCapturedSourceWords C u v w c d).card ≤
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card
    ∨
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card ≤
        (retainedCompletionWords C w).card := by
  rcases twoFlip_blocker_fullFree_or_halfCapture
      C hc hd with hfree | hhalf
  · exact Or.inr
      (overlap_card_le_blockerCompletion_of_fullFree
        C hfree)
  · exact Or.inl hhalf

#print axioms oneFlip_blocker_fullFree_or_halfCapture
#print axioms twoFlip_blocker_fullFree_or_halfCapture
#print axioms commonInactive_card_le_blocker_free_of_fullFree
#print axioms overlap_card_le_blockerCompletion_of_fullFree
#print axioms oneFlip_blocker_halfCapture_or_fullCapacity
#print axioms twoFlip_blocker_halfCapture_or_fullCapacity

end OrderedEdgeColoring
end JSP000404Research
