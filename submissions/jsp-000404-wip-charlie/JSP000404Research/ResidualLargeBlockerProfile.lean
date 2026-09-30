import JSP000404Research.ResidualTranslatedOverlapLargeCapture
import JSP000404Research.ResidualStrictOverlapPayment
import JSP000404Research.ResidualLossWords
import Mathlib.Tactic

/-!
# Profile classification of large translated-overlap blockers

Under the one-layer projected profile bound every vertex is exactly one of:

* strict: exponent < projectedFree;
* exact: exponent = projectedFree;
* projected-loss: exponent = projectedFree + 1.

For a large blocker of a translated overlap, strictness is immediately payable:
large capture implies the blocker completion cube is at least as large as the
whole source overlap, while strict profile surplus pays at least half of the
blocker cube. Therefore

  sourceOverlapMass <= 2 * surplus(blocker).

Thus every large blocker either contributes direct strict-surplus payment or
re-enters one of the two hard state classes: exact saturated or projected loss.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedProfile_strict_exact_or_loss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (w : V) :
    exponent w < projectedFree C w
    ∨ ExactProjectedBudget C exponent w
    ∨ w ∈ projectedLossVertices C exponent := by
  have hle :=
    exponent_le_projectedFree_add_one
      C exponent hexp honeLoss w
  by_cases hstrict : exponent w < projectedFree C w
  · exact Or.inl hstrict
  · by_cases hexact : exponent w = projectedFree C w
    · exact Or.inr (Or.inl hexact)
    · right
      right
      apply (mem_projectedLossVertices C exponent w).2
      omega

theorem large_oneFlip_strict_blocker_paid_by_two_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v w : V} {c : Fin n}
    (hc : c ∈ retainedActive C u)
    (hlarge :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        <
      2 * (oneFlipCapturedSourceWords C u v w c).card)
    (hstrict : exponent w < projectedFree C w) :
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card
      ≤
    2 * dyadicProfileSurplus exponent (projectedFree C) w := by
  have hcap :=
    overlap_card_le_blockerCompletion_of_large_oneFlip_capture
      C hc hlarge
  have hpay :=
    retainedCompletionWords_card_le_two_mul_surplus_of_strict
      C exponent hstrict
  exact hcap.trans hpay

theorem large_twoFlip_strict_blocker_paid_by_two_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v w : V} {c d : Fin n}
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v)
    (hlarge :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        <
      2 * (twoFlipCapturedSourceWords C u v w c d).card)
    (hstrict : exponent w < projectedFree C w) :
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card
      ≤
    2 * dyadicProfileSurplus exponent (projectedFree C) w := by
  have hcap :=
    overlap_card_le_blockerCompletion_of_large_twoFlip_capture
      C hc hd hlarge
  have hpay :=
    retainedCompletionWords_card_le_two_mul_surplus_of_strict
      C exponent hstrict
  exact hcap.trans hpay

theorem large_oneFlip_blocker_paid_or_exact_or_loss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {u v w : V} {c : Fin n}
    (hc : c ∈ retainedActive C u)
    (hlarge :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        <
      2 * (oneFlipCapturedSourceWords C u v w c).card) :
    (
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        ≤
      2 * dyadicProfileSurplus exponent (projectedFree C) w
    )
    ∨ ExactProjectedBudget C exponent w
    ∨ w ∈ projectedLossVertices C exponent := by
  rcases projectedProfile_strict_exact_or_loss
      C exponent hexp honeLoss w
    with hstrict | hexact | hloss
  · exact Or.inl
      (large_oneFlip_strict_blocker_paid_by_two_surplus
        C exponent hc hlarge hstrict)
  · exact Or.inr (Or.inl hexact)
  · exact Or.inr (Or.inr hloss)

theorem large_twoFlip_blocker_paid_or_exact_or_loss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {u v w : V} {c d : Fin n}
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v)
    (hlarge :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        <
      2 * (twoFlipCapturedSourceWords C u v w c d).card) :
    (
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        ≤
      2 * dyadicProfileSurplus exponent (projectedFree C) w
    )
    ∨ ExactProjectedBudget C exponent w
    ∨ w ∈ projectedLossVertices C exponent := by
  rcases projectedProfile_strict_exact_or_loss
      C exponent hexp honeLoss w
    with hstrict | hexact | hloss
  · exact Or.inl
      (large_twoFlip_strict_blocker_paid_by_two_surplus
        C exponent hc hd hlarge hstrict)
  · exact Or.inr (Or.inl hexact)
  · exact Or.inr (Or.inr hloss)

#print axioms projectedProfile_strict_exact_or_loss
#print axioms large_oneFlip_blocker_paid_or_exact_or_loss
#print axioms large_twoFlip_blocker_paid_or_exact_or_loss

end OrderedEdgeColoring
end JSP000404Research
