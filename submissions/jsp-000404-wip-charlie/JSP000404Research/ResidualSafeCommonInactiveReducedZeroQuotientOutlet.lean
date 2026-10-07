import JSP000404Research.ResidualSafeCommonInactiveReducedZeroOutlet
import JSP000404Research.ResidualReducedZeroFullRematchQuotient
import Mathlib.Tactic

/-!
# Quotient-aware reduced-zero outlet

The sharp reduced-zero outlet already isolates the only lossless branch to a
pair of distinct full blockers.  The rematch quotient sharpens that branch:

* either the common-inactive dimension strictly increases; or
* the new blocker-pair overlap is exactly the one-bit translate of the source
  overlap.

Thus every one-sided reduced-zero full-pair recursion has a genuine monotone
dimension step after quotienting stationary Boolean translations.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exists_leftReducedZero_oneFlip_quotient_outlet
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
          (retainedCompletionWords C u ∩
              retainedCompletionWords C v).image
                (fun word => flipBoolWordAt word c)
            =
          retainedCompletionWords C w ∩
            retainedCompletionWords C z
        ) := by
  classical
  obtain ⟨c,hcu,hcv,f,hf,hmap,hfullCard,hhalf,_hprofile,hpair⟩ :=
    exists_leftReducedZero_sharp_oneFlip_outlet
      C exponent hexp honeLoss
      hno huBase hvBase huSat hvSat huZero hvLt
  refine ⟨c,hcu,hcv,hfullCard,hhalf,?_⟩
  intro w z hw hz hwz
  exact
    oneFlip_two_fullBlockers_dimension_strict_or_translated_quotient
      C
      (Finset.mem_inter.mpr ⟨huBase,hvBase⟩)
      hcu hw hz hwz

theorem exists_rightReducedZero_oneFlip_quotient_outlet
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
          (retainedCompletionWords C u ∩
              retainedCompletionWords C v).image
                (fun word => flipBoolWordAt word c)
            =
          retainedCompletionWords C w ∩
            retainedCompletionWords C z
        ) := by
  classical
  obtain ⟨c,hcu,hcv,f,hf,hmap,hfullCard,hhalf,_hprofile,hpair⟩ :=
    exists_rightReducedZero_sharp_oneFlip_outlet
      C exponent hexp honeLoss
      hno huBase hvBase huSat hvSat hvZero huLt
  refine ⟨c,hcu,hcv,hfullCard,hhalf,?_⟩
  intro w z hw hz hwz
  exact
    oneFlip_two_fullBlockers_dimension_strict_or_translated_quotient
      C
      (Finset.mem_inter.mpr ⟨huBase,hvBase⟩)
      hcu hw hz hwz

#print axioms exists_leftReducedZero_oneFlip_quotient_outlet
#print axioms exists_rightReducedZero_oneFlip_quotient_outlet

end OrderedEdgeColoring
end JSP000404Research
