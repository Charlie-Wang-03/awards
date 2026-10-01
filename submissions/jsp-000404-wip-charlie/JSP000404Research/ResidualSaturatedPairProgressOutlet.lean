import JSP000404Research.ResidualCommonInactiveSharpOutlet
import JSP000404Research.ResidualFullPairProfileReduction
import JSP000404Research.ResidualFullPairProgress
import Mathlib.Tactic

/-!
# Saturated-pair progress outlet

Combine the sharp local blocker trichotomy with the profile reduction and the
full-pair progress theorem.

For an exact--exact source pair with both exponents < n there is one fixed
injective one- or two-bit displacement of the whole overlap cube such that:

* every non-full blocker captures at most half of the source overlap mass;
* there are at most two full blockers;
* every full blocker is strict-credit, exact, or projected-loss;
* if two distinct full blockers are both exact, then their residual-pair
  overlap either
    - has the same mass, in which case the fixed translation is a bijective
      rematching of the two overlap cubes, or
    - has strictly larger common-inactive dimension.

Thus every genuinely recursive lossless saturated transition either is
reversible or strictly increases a dimension bounded by n.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exists_saturated_pair_progress_outlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
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
            (oneFlipFullBlockers C u v c).card ≤ 2 ∧
            (∀ w : V,
              w ∉ oneFlipFullBlockers C u v c →
              2 * (oneFlipCapturedSourceWords C u v w c).card ≤
                (retainedCompletionWords C u ∩
                  retainedCompletionWords C v).card) ∧
            (∀ w : V,
              w ∈ oneFlipFullBlockers C u v c →
              (
                exponent w < projectedFree C w
                ∨ ExactProjectedBudget C exponent w
                ∨ w ∈ projectedLossVertices C exponent
              )) ∧
            (∀ w z : V,
              w ∈ oneFlipFullBlockers C u v c →
              z ∈ oneFlipFullBlockers C u v c →
              w ≠ z →
              ExactProjectedBudget C exponent w →
              ExactProjectedBudget C exponent z →
              (
                (
                  (retainedCompletionWords C u ∩
                    retainedCompletionWords C v).card =
                  (retainedCompletionWords C w ∩
                    retainedCompletionWords C z).card
                  ∧
                  ∃ e :
                    {x : Fin n → Bool //
                      x ∈ retainedCompletionWords C u ∩
                        retainedCompletionWords C v} ≃
                    {y : Fin n → Bool //
                      y ∈ retainedCompletionWords C w ∩
                        retainedCompletionWords C z},
                    ∀ x, (e x).1 = flipBoolWordAt x.1 c
                )
                ∨
                (commonInactiveRetained C u v).card <
                  (commonInactiveRetained C w z).card
              ))
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
            (twoFlipFullBlockers C u v c d).card ≤ 2 ∧
            (∀ w : V,
              w ∉ twoFlipFullBlockers C u v c d →
              2 * (twoFlipCapturedSourceWords C u v w c d).card ≤
                (retainedCompletionWords C u ∩
                  retainedCompletionWords C v).card) ∧
            (∀ w : V,
              w ∈ twoFlipFullBlockers C u v c d →
              (
                exponent w < projectedFree C w
                ∨ ExactProjectedBudget C exponent w
                ∨ w ∈ projectedLossVertices C exponent
              )) ∧
            (∀ w z : V,
              w ∈ twoFlipFullBlockers C u v c d →
              z ∈ twoFlipFullBlockers C u v c d →
              w ≠ z →
              ExactProjectedBudget C exponent w →
              ExactProjectedBudget C exponent z →
              (
                (
                  (retainedCompletionWords C u ∩
                    retainedCompletionWords C v).card =
                  (retainedCompletionWords C w ∩
                    retainedCompletionWords C z).card
                  ∧
                  ∃ e :
                    {x : Fin n → Bool //
                      x ∈ retainedCompletionWords C u ∩
                        retainedCompletionWords C v} ≃
                    {y : Fin n → Bool //
                      y ∈ retainedCompletionWords C w ∩
                        retainedCompletionWords C z},
                    ∀ x,
                      (e x).1 =
                        flipBoolWordAt (flipBoolWordAt x.1 c) d
                )
                ∨
                (commonInactiveRetained C u v).card <
                  (commonInactiveRetained C w z).card
              ))
        )
      ) := by
  classical
  obtain ⟨f,hf,hshape⟩ :=
    exists_saturated_pair_sharp_recursive_outlet
      C exponent hexp honeLoss hbase huSat hvSat huLt hvLt
  refine ⟨f,hf,?_⟩
  rcases hshape with hone | htwo
  · left
    obtain ⟨c,hcu,hcv,hmap,hcard,hhalf,hprofile,_hpair⟩ := hone
    refine ⟨c,hcu,hcv,hmap,hcard,hhalf,?_,?_⟩
    · intro w hw
      rcases hprofile w hw with hstrictPaid | hexact | hloss
      · left
        by_contra hnot
        have hle : projectedFree C w ≤ exponent w := by omega
        have hsurZero :
            dyadicProfileSurplus exponent (projectedFree C) w = 0 := by
          unfold dyadicProfileSurplus
          have hp :
              2 ^ projectedFree C w ≤ 2 ^ exponent w :=
            Nat.pow_le_pow_right (by norm_num : 0 < 2) hle
          omega
        rw [hsurZero] at hstrictPaid
        omega
      · exact Or.inr (Or.inl hexact)
      · exact Or.inr (Or.inr hloss)
    · intro w z hw hz hwz hwExact hzExact
      exact
        oneFlip_two_fullBlockers_equal_rematch_or_dimension_increases
          C hbase hcu hw hz hwz
  · right
    obtain ⟨c,d,hcd,hcu,hdv,hmap,hcard,hhalf,hprofile,_hpair⟩ := htwo
    refine ⟨c,d,hcd,hcu,hdv,hmap,hcard,hhalf,?_,?_⟩
    · intro w hw
      rcases hprofile w hw with hstrictPaid | hexact | hloss
      · left
        by_contra hnot
        have hle : projectedFree C w ≤ exponent w := by omega
        have hsurZero :
            dyadicProfileSurplus exponent (projectedFree C) w = 0 := by
          unfold dyadicProfileSurplus
          have hp :
              2 ^ projectedFree C w ≤ 2 ^ exponent w :=
            Nat.pow_le_pow_right (by norm_num : 0 < 2) hle
          omega
        rw [hsurZero] at hstrictPaid
        omega
      · exact Or.inr (Or.inl hexact)
      · exact Or.inr (Or.inr hloss)
    · intro w z hw hz hwz hwExact hzExact
      exact
        twoFlip_two_fullBlockers_equal_rematch_or_dimension_increases
          C hbase hcu hdv hw hz hwz

#print axioms exists_saturated_pair_progress_outlet

end OrderedEdgeColoring
end JSP000404Research
