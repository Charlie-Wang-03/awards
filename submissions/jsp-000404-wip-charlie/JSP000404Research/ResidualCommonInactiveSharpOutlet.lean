import JSP000404Research.ResidualSaturatedPairCollisionControl
import JSP000404Research.ResidualTranslatedOverlapCaptureTrichotomy
import JSP000404Research.ResidualTranslatedOverlapFullBranch
import JSP000404Research.ResidualTranslatedOverlapFullPair
import JSP000404Research.ResidualLargeBlockerProfile
import Mathlib.Tactic

/-!
# Sharp recursive outlet for saturated overlap carriers

For a saturated overlap carrier with a chosen base word, the explicit pair-local
injection admits an exact blocker trichotomy:

  capture = 0,
  capture = full source mass,
  or capture <= half source mass.

The full blockers are at most two.  Every full blocker is a large blocker, so
its projected profile is either strict-credit, exact, or projected-loss.

If two distinct full blockers exist, they form a residual pair, inherit every
common-inactive source coordinate, and their completion-cube intersection has
cardinality at least the source overlap mass.

Thus every non-full branch loses a factor two, while every lossless branch is
forced into an explicitly controlled residual-pair state.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exists_saturated_pair_sharp_recursive_outlet
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
                (retainedCompletionWords C u ∩
                  retainedCompletionWords C v).card ≤
                  2 * dyadicProfileSurplus
                    exponent (projectedFree C) w
              )
              ∨ ExactProjectedBudget C exponent w
              ∨ w ∈ projectedLossVertices C exponent) ∧
            (∀ w z : V,
              w ∈ oneFlipFullBlockers C u v c →
              z ∈ oneFlipFullBlockers C u v c →
              w ≠ z →
              (
                ((w < z ∧ IsResidual C w z) ∨
                  (z < w ∧ IsResidual C z w)) ∧
                commonInactiveRetained C u v ⊆
                  commonInactiveRetained C w z ∧
                (retainedCompletionWords C u ∩
                  retainedCompletionWords C v).card ≤
                  (retainedCompletionWords C w ∩
                    retainedCompletionWords C z).card
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
                (retainedCompletionWords C u ∩
                  retainedCompletionWords C v).card ≤
                  2 * dyadicProfileSurplus
                    exponent (projectedFree C) w
              )
              ∨ ExactProjectedBudget C exponent w
              ∨ w ∈ projectedLossVertices C exponent) ∧
            (∀ w z : V,
              w ∈ twoFlipFullBlockers C u v c d →
              z ∈ twoFlipFullBlockers C u v c d →
              w ≠ z →
              (
                ((w < z ∧ IsResidual C w z) ∨
                  (z < w ∧ IsResidual C z w)) ∧
                commonInactiveRetained C u v ⊆
                  commonInactiveRetained C w z ∧
                (retainedCompletionWords C u ∩
                  retainedCompletionWords C v).card ≤
                  (retainedCompletionWords C w ∩
                    retainedCompletionWords C z).card
              ))
        )
      ) := by
  classical
  obtain ⟨f,hf,hshape⟩ :=
    exists_saturated_pair_injection_with_blocker_control
      C exponent huSat hvSat huLt hvLt
  refine ⟨f,hf,?_⟩
  rcases hshape with hone | htwo
  · left
    obtain ⟨c,hcu,hcv,hmap,_hcontrol⟩ := hone
    refine ⟨c,hcu,hcv,hmap,
      oneFlip_fullBlockers_card_le_two C hbase,?_,?_,?_⟩
    · intro w hwNotFull
      rcases oneFlip_capture_zero_full_or_half C hcu
        with hzero | hfull | hhalf
      · omega
      · exfalso
        exact hwNotFull
          ((mem_oneFlipFullBlockers C u v c w).2 hfull)
      · exact hhalf
    · intro w hwFull
      have hfull :=
        (mem_oneFlipFullBlockers C u v c w).1 hwFull
      have hpos :
          0 < (retainedCompletionWords C u ∩
            retainedCompletionWords C v).card :=
        Finset.card_pos.mpr ⟨base,hbase⟩
      have hlarge :
          (retainedCompletionWords C u ∩
            retainedCompletionWords C v).card
            <
          2 * (oneFlipCapturedSourceWords C u v w c).card := by
        rw [hfull]
        omega
      exact large_oneFlip_blocker_paid_or_exact_or_loss
        C exponent hexp honeLoss hcu hlarge
    · intro w z hw hz hwz
      refine ⟨
        oneFlip_two_fullBlockers_form_residual_pair
          C hbase hw hz hwz,
        oneFlip_two_fullBlockers_inherit_commonInactive
          C hbase hcu hw hz,
        oneFlip_source_overlap_card_le_two_fullBlocker_intersection
          C hw hz⟩
  · right
    obtain ⟨c,d,hcd,hcu,hdv,hmap,_hcontrol⟩ := htwo
    refine ⟨c,d,hcd,hcu,hdv,hmap,
      twoFlip_fullBlockers_card_le_two C hbase,?_,?_,?_⟩
    · intro w hwNotFull
      rcases twoFlip_capture_zero_full_or_half C hcu hdv
        with hzero | hfull | hhalf
      · omega
      · exfalso
        exact hwNotFull
          ((mem_twoFlipFullBlockers C u v c d w).2 hfull)
      · exact hhalf
    · intro w hwFull
      have hfull :=
        (mem_twoFlipFullBlockers C u v c d w).1 hwFull
      have hpos :
          0 < (retainedCompletionWords C u ∩
            retainedCompletionWords C v).card :=
        Finset.card_pos.mpr ⟨base,hbase⟩
      have hlarge :
          (retainedCompletionWords C u ∩
            retainedCompletionWords C v).card
            <
          2 * (twoFlipCapturedSourceWords C u v w c d).card := by
        rw [hfull]
        omega
      exact large_twoFlip_blocker_paid_or_exact_or_loss
        C exponent hexp honeLoss hcu hdv hlarge
    · intro w z hw hz hwz
      refine ⟨
        twoFlip_two_fullBlockers_form_residual_pair
          C hbase hw hz hwz,
        twoFlip_two_fullBlockers_inherit_commonInactive
          C hbase hcu hdv hw hz,
        twoFlip_source_overlap_card_le_two_fullBlocker_intersection
          C hw hz⟩

#print axioms exists_saturated_pair_sharp_recursive_outlet

end OrderedEdgeColoring
end JSP000404Research
