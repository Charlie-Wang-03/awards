import JSP000404Research.ResidualSafeCommonInactiveReducedZeroQuotientOutlet
import JSP000404Research.ResidualReducedZeroOverlapTranslationQuotient
import Mathlib.Tactic

/-!
# Reduced-zero outlet in overlap-translation quotient form

The raw quotient-aware reduced-zero outlet returns, for two distinct full
blockers, either strict common-inactive dimension growth or an explicit
one-coordinate translate equality of overlap cubes.

This module packages the latter as equality in
OverlapTranslationQuotient.  The recursive branch is therefore expressed in
the exact state space needed for later termination / induction arguments.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exists_leftReducedZero_oneFlip_overlapQuotient_outlet
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
      ∀ w z : V,
        w ∈ oneFlipFullBlockers C u v c →
        z ∈ oneFlipFullBlockers C u v c →
        w ≠ z →
        (
          (commonInactiveRetained C u v).card <
            (commonInactiveRetained C w z).card
          ∨
          Quotient.mk
              (overlapTranslationSetoid n)
              (retainedCompletionWords C u ∩
                retainedCompletionWords C v)
            =
          Quotient.mk
              (overlapTranslationSetoid n)
              (retainedCompletionWords C w ∩
                retainedCompletionWords C z)
        ) := by
  obtain ⟨c,hcu,hcv,hfullCard,hhalf,hpair⟩ :=
    exists_leftReducedZero_oneFlip_quotient_outlet
      C exponent hexp honeLoss
      hno huBase hvBase huSat hvSat huZero hvLt
  refine ⟨c,hcu,hcv,hfullCard,hhalf,?_⟩
  intro w z hw hz hwz
  exact
    oneFlip_two_fullBlockers_dimension_strict_or_same_overlap_quotient
      C
      (Finset.mem_inter.mpr ⟨huBase,hvBase⟩)
      hcu hw hz hwz

theorem exists_rightReducedZero_oneFlip_overlapQuotient_outlet
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
      ∀ w z : V,
        w ∈ oneFlipFullBlockers C u v c →
        z ∈ oneFlipFullBlockers C u v c →
        w ≠ z →
        (
          (commonInactiveRetained C u v).card <
            (commonInactiveRetained C w z).card
          ∨
          Quotient.mk
              (overlapTranslationSetoid n)
              (retainedCompletionWords C u ∩
                retainedCompletionWords C v)
            =
          Quotient.mk
              (overlapTranslationSetoid n)
              (retainedCompletionWords C w ∩
                retainedCompletionWords C z)
        ) := by
  obtain ⟨c,hcu,hcv,hfullCard,hhalf,hpair⟩ :=
    exists_rightReducedZero_oneFlip_quotient_outlet
      C exponent hexp honeLoss
      hno huBase hvBase huSat hvSat hvZero huLt
  refine ⟨c,hcu,hcv,hfullCard,hhalf,?_⟩
  intro w z hw hz hwz
  exact
    oneFlip_two_fullBlockers_dimension_strict_or_same_overlap_quotient
      C
      (Finset.mem_inter.mpr ⟨huBase,hvBase⟩)
      hcu hw hz hwz

#print axioms exists_leftReducedZero_oneFlip_overlapQuotient_outlet
#print axioms exists_rightReducedZero_oneFlip_overlapQuotient_outlet

end OrderedEdgeColoring
end JSP000404Research
