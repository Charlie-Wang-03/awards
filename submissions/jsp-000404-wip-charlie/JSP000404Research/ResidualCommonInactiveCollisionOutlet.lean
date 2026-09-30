import JSP000404Research.ResidualSaturatedPairCollisionControl
import JSP000404Research.ResidualPairLargeBlockers
import Mathlib.Tactic

/-!
# Quantitative outlet for the common-inactive saturated carrier

This packages the current collision analysis for one saturated overlap pair
into the form needed by the eventual global charging argument.

There is one fixed injective one- or two-bit displacement of the whole source
overlap cube. In either branch:

* at most three blocker vertices are large;
* every non-large blocker captures at most half the source mass;
* every large blocker has completion capacity at least the entire source
  overlap mass.

Thus the only dimension-preserving branches have constant fan-out; all other
collision branches lose a factor two.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exists_saturated_pair_quantitative_collision_outlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
              (retainedCompletionWords C u ∩
                retainedCompletionWords C v).card ≤
                  (retainedCompletionWords C w).card)
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
              (retainedCompletionWords C u ∩
                retainedCompletionWords C v).card ≤
                  (retainedCompletionWords C w).card)
        )
      ) := by
  obtain ⟨f,hf,hshape⟩ :=
    exists_saturated_pair_injection_with_blocker_control
      C exponent huSat hvSat huLt hvLt
  refine ⟨f,hf,?_⟩
  rcases hshape with hone | htwo
  · left
    obtain ⟨c,hcu,hcv,hmap,hcontrol⟩ := hone
    refine ⟨c,hcu,hcv,hmap,
      oneFlipLargeBlockers_card_le_three C u v c,?_,?_⟩
    · intro w hwNotLarge
      have hnot :
          ¬ (
            (retainedCompletionWords C u ∩
              retainedCompletionWords C v).card
              <
            2 * (oneFlipCapturedSourceWords C u v w c).card) := by
        intro hlt
        exact hwNotLarge
          ((mem_oneFlipLargeBlockers C u v w c).2 hlt)
      omega
    · intro w hwLarge
      have hlarge :=
        (mem_oneFlipLargeBlockers C u v w c).1 hwLarge
      exact
        overlap_card_le_blockerCompletion_of_large_oneFlip_capture
          C hcu hlarge
  · right
    obtain ⟨c,d,hcd,hcu,hdv,hmap,hcontrol⟩ := htwo
    refine ⟨c,d,hcd,hcu,hdv,hmap,
      twoFlipLargeBlockers_card_le_three C u v c d,?_,?_⟩
    · intro w hwNotLarge
      have hnot :
          ¬ (
            (retainedCompletionWords C u ∩
              retainedCompletionWords C v).card
              <
            2 * (twoFlipCapturedSourceWords C u v w c d).card) := by
        intro hlt
        exact hwNotLarge
          ((mem_twoFlipLargeBlockers C u v w c d).2 hlt)
      omega
    · intro w hwLarge
      have hlarge :=
        (mem_twoFlipLargeBlockers C u v w c d).1 hwLarge
      exact
        overlap_card_le_blockerCompletion_of_large_twoFlip_capture
          C hcu hdv hlarge

#print axioms exists_saturated_pair_quantitative_collision_outlet

end OrderedEdgeColoring
end JSP000404Research
