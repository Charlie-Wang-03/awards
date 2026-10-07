import JSP000404Research.ResidualSafeCommonInactiveNestedExit
import JSP000404Research.ResidualTranslatedOverlapCaptureTrichotomy
import JSP000404Research.ResidualTranslatedOverlapFullBranch
import JSP000404Research.ResidualTranslatedOverlapFullPair
import JSP000404Research.ResidualLargeBlockerProfile
import Mathlib.Tactic

/-!
# Sharp outlet for one-sided reduced-zero nested overlap blocks

A one-sided reduced-zero NoActiveSafe saturated pair is nested.  Under the
concrete all-N hypothesis that the opposite exact endpoint has exponent < n,
there is one retained coordinate active at both endpoints.  Flipping that
coordinate gives one fixed injective translation of the entire overlap block
outside both endpoint cubes.

For this fixed translation every blocker has the exact 0/full/half trichotomy.
Consequently:

* every non-full blocker captures at most half of the source block;
* there are at most two full blockers;
* every full blocker is strict, exact, or projected-loss;
* two distinct full blockers form a new residual pair, inherit every source
  common-inactive coordinate, and carry overlap mass at least the source mass.

This isolates the only lossless recursive branch to an exact--exact full
blocker pair.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exists_leftReducedZero_sharp_oneFlip_outlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V} {base : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huZero :
      exponent u = (commonInactiveRetained C u v).card)
    (hvLt : exponent v < n) :
    ∃ c : Fin n,
      c ∈ retainedActive C u ∧
      c ∈ retainedActive C v ∧
      ∃ f :
        {word : Fin n → Bool //
          word ∈ retainedCompletionWords C u ∩
            retainedCompletionWords C v} →
        {word : Fin n → Bool //
          word ∈ pairLocalHoles C u v},
        Function.Injective f ∧
        (∀ word, (f word).1 = flipBoolWordAt word.1 c) ∧
        (oneFlipFullBlockers C u v c).card ≤ 2 ∧
        (∀ w : V,
          w ∉ oneFlipFullBlockers C u v c →
          2 * (oneFlipCapturedSourceWords C u v w c).card ≤
            (retainedCompletionWords C u ∩
              retainedCompletionWords C v).card) ∧
        (∀ w : V,
          w ∈ oneFlipFullBlockers C u v c →
          exponent w < projectedFree C w
          ∨ ExactProjectedBudget C exponent w
          ∨ w ∈ projectedLossVertices C exponent) ∧
        ∀ w z : V,
          w ∈ oneFlipFullBlockers C u v c →
          z ∈ oneFlipFullBlockers C u v c →
          w ≠ z →
          (((w < z ∧ IsResidual C w z) ∨
            (z < w ∧ IsResidual C z w)) ∧
           commonInactiveRetained C u v ⊆
             commonInactiveRetained C w z ∧
           (retainedCompletionWords C u ∩
             retainedCompletionWords C v).card ≤
             (retainedCompletionWords C w ∩
               retainedCompletionWords C z).card) := by
  classical
  obtain ⟨c,hcu,hcv,f,hf,hmap⟩ :=
    exists_nested_left_reducedZero_oneFlip_exit
      C exponent hno huBase hvBase huSat hvSat huZero hvLt
  refine ⟨c,hcu,hcv,f,hf,hmap,
    oneFlip_fullBlockers_card_le_two
      C (Finset.mem_inter.mpr ⟨huBase,hvBase⟩),?_,?_,?_⟩
  · intro w hwNotFull
    rcases oneFlip_capture_zero_full_or_half C hcu
      with hzero | hfull | hhalf
    · simpa [hzero]
    · exfalso
      exact hwNotFull
        ((mem_oneFlipFullBlockers C u v c w).2 hfull)
    · exact hhalf
  · intro w hwFull
    exact projectedProfile_strict_exact_or_loss
      C exponent hexp honeLoss w
  · intro w z hw hz hwz
    exact ⟨
      oneFlip_two_fullBlockers_form_residual_pair
        C (Finset.mem_inter.mpr ⟨huBase,hvBase⟩) hw hz hwz,
      oneFlip_two_fullBlockers_inherit_commonInactive
        C (Finset.mem_inter.mpr ⟨huBase,hvBase⟩) hcu hw hz,
      oneFlip_source_overlap_card_le_two_fullBlocker_intersection
        C hw hz⟩

theorem exists_rightReducedZero_sharp_oneFlip_outlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V} {base : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (hvZero :
      exponent v = (commonInactiveRetained C u v).card)
    (huLt : exponent u < n) :
    ∃ c : Fin n,
      c ∈ retainedActive C u ∧
      c ∈ retainedActive C v ∧
      ∃ f :
        {word : Fin n → Bool //
          word ∈ retainedCompletionWords C u ∩
            retainedCompletionWords C v} →
        {word : Fin n → Bool //
          word ∈ pairLocalHoles C u v},
        Function.Injective f ∧
        (∀ word, (f word).1 = flipBoolWordAt word.1 c) ∧
        (oneFlipFullBlockers C u v c).card ≤ 2 ∧
        (∀ w : V,
          w ∉ oneFlipFullBlockers C u v c →
          2 * (oneFlipCapturedSourceWords C u v w c).card ≤
            (retainedCompletionWords C u ∩
              retainedCompletionWords C v).card) ∧
        (∀ w : V,
          w ∈ oneFlipFullBlockers C u v c →
          exponent w < projectedFree C w
          ∨ ExactProjectedBudget C exponent w
          ∨ w ∈ projectedLossVertices C exponent) ∧
        ∀ w z : V,
          w ∈ oneFlipFullBlockers C u v c →
          z ∈ oneFlipFullBlockers C u v c →
          w ≠ z →
          (((w < z ∧ IsResidual C w z) ∨
            (z < w ∧ IsResidual C z w)) ∧
           commonInactiveRetained C u v ⊆
             commonInactiveRetained C w z ∧
           (retainedCompletionWords C u ∩
             retainedCompletionWords C v).card ≤
             (retainedCompletionWords C w ∩
               retainedCompletionWords C z).card) := by
  classical
  obtain ⟨c,hcu,hcv,f,hf,hmap⟩ :=
    exists_nested_right_reducedZero_oneFlip_exit
      C exponent hno huBase hvBase huSat hvSat hvZero huLt
  refine ⟨c,hcu,hcv,f,hf,hmap,
    oneFlip_fullBlockers_card_le_two
      C (Finset.mem_inter.mpr ⟨huBase,hvBase⟩),?_,?_,?_⟩
  · intro w hwNotFull
    rcases oneFlip_capture_zero_full_or_half C hcu
      with hzero | hfull | hhalf
    · simpa [hzero]
    · exfalso
      exact hwNotFull
        ((mem_oneFlipFullBlockers C u v c w).2 hfull)
    · exact hhalf
  · intro w hwFull
    exact projectedProfile_strict_exact_or_loss
      C exponent hexp honeLoss w
  · intro w z hw hz hwz
    exact ⟨
      oneFlip_two_fullBlockers_form_residual_pair
        C (Finset.mem_inter.mpr ⟨huBase,hvBase⟩) hw hz hwz,
      oneFlip_two_fullBlockers_inherit_commonInactive
        C (Finset.mem_inter.mpr ⟨huBase,hvBase⟩) hcu hw hz,
      oneFlip_source_overlap_card_le_two_fullBlocker_intersection
        C hw hz⟩

#print axioms exists_leftReducedZero_sharp_oneFlip_outlet
#print axioms exists_rightReducedZero_sharp_oneFlip_outlet

end OrderedEdgeColoring
end JSP000404Research
