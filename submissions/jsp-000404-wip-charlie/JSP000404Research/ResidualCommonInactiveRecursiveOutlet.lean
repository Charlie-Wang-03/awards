import JSP000404Research.ResidualCommonInactiveCollisionOutlet
import JSP000404Research.ResidualLargeBlockerProfile
import Mathlib.Tactic

/-!
# Recursive outlet for a saturated pair with common-inactive freedom

Combine the quantitative collision outlet with the projected-profile
classification of large blockers.

For one fixed injective displacement of the whole saturated overlap cube:

* every non-large blocker captures at most half the source mass;
* there are at most three large blockers;
* every large blocker is either
  - directly paid by at most twice its strict profile surplus,
  - exact projected budget, hence a saturated hard state,
  - projected loss, hence a loss hard state.

Thus the common-inactive saturated subtype is closed under a finite weighted
branching recursion whose only unpaid large descendants are the two already
identified hard state classes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exists_saturated_pair_recursive_collision_outlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {u v : V}
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huLt : exponent u < n)
    (hvLt : exponent v < n) :
    ∃ f :
      {word : Fin n → Bool //
        word ∈ retainedCompletionWords C u ∩
          retainedCompletionWords C v} →
      {word : Fin n → Bool //
        word ∈ pairLocalHoles C u v},
      Function.Injective f ∧
      (
        (
          ∃ c : Fin n,
            c ∈ retainedActive C u ∧
            c ∈ retainedActive C v ∧
            (∀ word,
              (f word).1 = flipBoolWordAt word.1 c) ∧
            (oneFlipLargeBlockers C u v c).card ≤ 3 ∧
            (∀ w : V,
              w ∉ oneFlipLargeBlockers C u v c →
              2 * (oneFlipCapturedSourceWords C u v w c).card ≤
                (retainedCompletionWords C u ∩
                  retainedCompletionWords C v).card) ∧
            (∀ w : V,
              w ∈ oneFlipLargeBlockers C u v c →
              (
                (retainedCompletionWords C u ∩
                  retainedCompletionWords C v).card
                  ≤
                2 * dyadicProfileSurplus
                  exponent (projectedFree C) w
              )
              ∨ ExactProjectedBudget C exponent w
              ∨ w ∈ projectedLossVertices C exponent)
        )
        ∨
        (
          ∃ c d : Fin n,
            c ≠ d ∧
            c ∈ retainedActive C u ∧
            d ∈ retainedActive C v ∧
            (∀ word,
              (f word).1 =
                flipBoolWordAt
                  (flipBoolWordAt word.1 c) d) ∧
            (twoFlipLargeBlockers C u v c d).card ≤ 3 ∧
            (∀ w : V,
              w ∉ twoFlipLargeBlockers C u v c d →
              2 * (twoFlipCapturedSourceWords C u v w c d).card ≤
                (retainedCompletionWords C u ∩
                  retainedCompletionWords C v).card) ∧
            (∀ w : V,
              w ∈ twoFlipLargeBlockers C u v c d →
              (
                (retainedCompletionWords C u ∩
                  retainedCompletionWords C v).card
                  ≤
                2 * dyadicProfileSurplus
                  exponent (projectedFree C) w
              )
              ∨ ExactProjectedBudget C exponent w
              ∨ w ∈ projectedLossVertices C exponent)
        )
      ) := by
  obtain ⟨f,hf,hshape⟩ :=
    exists_saturated_pair_quantitative_collision_outlet
      C exponent huSat hvSat huLt hvLt
  refine ⟨f,hf,?_⟩
  rcases hshape with hone | htwo
  · left
    obtain ⟨c,hcu,hcv,hmap,hcard,hsmall,hlargeCap⟩ := hone
    refine ⟨c,hcu,hcv,hmap,hcard,hsmall,?_⟩
    intro w hwLarge
    have hlarge :=
      (mem_oneFlipLargeBlockers C u v w c).1 hwLarge
    exact large_oneFlip_blocker_paid_or_exact_or_loss
      C exponent hexp honeLoss hcu hlarge
  · right
    obtain ⟨c,d,hcd,hcu,hdv,hmap,hcard,hsmall,hlargeCap⟩ := htwo
    refine ⟨c,d,hcd,hcu,hdv,hmap,hcard,hsmall,?_⟩
    intro w hwLarge
    have hlarge :=
      (mem_twoFlipLargeBlockers C u v w c d).1 hwLarge
    exact large_twoFlip_blocker_paid_or_exact_or_loss
      C exponent hexp honeLoss hcu hdv hlarge

#print axioms exists_saturated_pair_recursive_collision_outlet

end OrderedEdgeColoring
end JSP000404Research
