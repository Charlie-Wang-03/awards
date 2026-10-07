import JSP000404Research.ResidualSafeCommonInactiveReducedZeroOutlet
import JSP000404Research.ResidualReducedZeroOverlapTranslationQuotient
import JSP000404Research.ResidualOverlapTranslationSupport
import Mathlib.Tactic

/-!
# Profiled stationary outlet for one-sided reduced-zero overlap recursion

The sharp one-flip outlet already classifies every full blocker as

* strict projected surplus,
* exact projected budget, or
* projected loss.

The overlap-translation quotient sharpens every pair of distinct full blockers:

* either the common-inactive support grows strictly in cardinality;
* or the overlap stays in the same translation quotient.

The varying-coordinate invariant strengthens the stationary branch further:
same quotient forces equality of the entire common-inactive support set.

Thus the only genuinely stationary recursive branch that is not already paid
by strict surplus or delegated to projected-loss handling is exact--exact with
the same common-inactive support.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exists_leftReducedZero_profiled_stationary_outlet
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
        (
          ((w < z ∧ IsResidual C w z) ∨
            (z < w ∧ IsResidual C z w))
          ∧
          (
            (commonInactiveRetained C u v).card <
              (commonInactiveRetained C w z).card
            ∨
            (
              Quotient.mk
                  (overlapTranslationSetoid n)
                  (retainedCompletionWords C u ∩
                    retainedCompletionWords C v)
                =
              Quotient.mk
                  (overlapTranslationSetoid n)
                  (retainedCompletionWords C w ∩
                    retainedCompletionWords C z)
              ∧
              commonInactiveRetained C u v =
                commonInactiveRetained C w z
            )
          )
        ) := by
  classical
  obtain
      ⟨c,hcu,hcv,f,hf,hmap,hfullCard,hhalf,hprofile,hpair⟩ :=
    exists_leftReducedZero_sharp_oneFlip_outlet
      C exponent hexp honeLoss
      hno huBase hvBase huSat hvSat huZero hvLt
  refine ⟨c,hcu,hcv,hfullCard,hhalf,hprofile,?_⟩
  intro w z hw hz hwz
  have hres := (hpair w z hw hz hwz).1
  refine ⟨hres,?_⟩
  rcases
      oneFlip_two_fullBlockers_dimension_strict_or_same_overlap_quotient
        C
        (Finset.mem_inter.mpr ⟨huBase,hvBase⟩)
        hcu hw hz hwz
    with hdim | hq
  · exact Or.inl hdim
  · right
    have hwBase :
        flipBoolWordAt base c ∈ retainedCompletionWords C w :=
      oneFlip_fullBlocker_contains_base
        C (Finset.mem_inter.mpr ⟨huBase,hvBase⟩) hw
    have hzBase :
        flipBoolWordAt base c ∈ retainedCompletionWords C z :=
      oneFlip_fullBlocker_contains_base
        C (Finset.mem_inter.mpr ⟨huBase,hvBase⟩) hz
    have hsupport :=
      overlap_same_translation_quotient_commonRetainedInactive_eq
        C huBase hvBase hwBase hzBase hq
    exact ⟨hq,hsupport⟩

theorem exists_rightReducedZero_profiled_stationary_outlet
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
        (
          ((w < z ∧ IsResidual C w z) ∨
            (z < w ∧ IsResidual C z w))
          ∧
          (
            (commonInactiveRetained C u v).card <
              (commonInactiveRetained C w z).card
            ∨
            (
              Quotient.mk
                  (overlapTranslationSetoid n)
                  (retainedCompletionWords C u ∩
                    retainedCompletionWords C v)
                =
              Quotient.mk
                  (overlapTranslationSetoid n)
                  (retainedCompletionWords C w ∩
                    retainedCompletionWords C z)
              ∧
              commonInactiveRetained C u v =
                commonInactiveRetained C w z
            )
          )
        ) := by
  classical
  obtain
      ⟨c,hcu,hcv,f,hf,hmap,hfullCard,hhalf,hprofile,hpair⟩ :=
    exists_rightReducedZero_sharp_oneFlip_outlet
      C exponent hexp honeLoss
      hno huBase hvBase huSat hvSat hvZero huLt
  refine ⟨c,hcu,hcv,hfullCard,hhalf,hprofile,?_⟩
  intro w z hw hz hwz
  have hres := (hpair w z hw hz hwz).1
  refine ⟨hres,?_⟩
  rcases
      oneFlip_two_fullBlockers_dimension_strict_or_same_overlap_quotient
        C
        (Finset.mem_inter.mpr ⟨huBase,hvBase⟩)
        hcu hw hz hwz
    with hdim | hq
  · exact Or.inl hdim
  · right
    have hwBase :
        flipBoolWordAt base c ∈ retainedCompletionWords C w :=
      oneFlip_fullBlocker_contains_base
        C (Finset.mem_inter.mpr ⟨huBase,hvBase⟩) hw
    have hzBase :
        flipBoolWordAt base c ∈ retainedCompletionWords C z :=
      oneFlip_fullBlocker_contains_base
        C (Finset.mem_inter.mpr ⟨huBase,hvBase⟩) hz
    have hsupport :=
      overlap_same_translation_quotient_commonRetainedInactive_eq
        C huBase hvBase hwBase hzBase hq
    exact ⟨hq,hsupport⟩

#print axioms exists_leftReducedZero_profiled_stationary_outlet
#print axioms exists_rightReducedZero_profiled_stationary_outlet

end OrderedEdgeColoring
end JSP000404Research
