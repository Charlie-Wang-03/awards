import JSP000404Research.ResidualUnsafeSaturatedWordClassification
import JSP000404Research.ResidualZeroZeroRecursiveOutlet
import Mathlib.Tactic

/-!
# Unified recursive outlet for unsafe saturated hard words

The unsafe saturated word classifier has two branches:

* a nonzero exact endpoint gives a one-step safe residual descent;
* the only terminal local carrier type is zero--zero.

The zero--zero blocker-star theorem refines that terminal type further:
one gets either an immediate Boolean hole, one unit of strict profile surplus,
or an injective family of exact/loss blockers.

This module packages both results into one recursive hard-state alphabet.
It is deliberately word-local; the remaining task is the global
well-founded / augmenting payment that combines these local outlets.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A one-step safe displacement of an unsafe saturated word. -/
def UnsafeSaturatedSafeDescent
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (word : Fin n → Bool) : Prop :=
  ∃ u v : V,
    u < v ∧
    word ∈ retainedCompletionWords C u ∧
    word ∈ retainedCompletionWords C v ∧
    (
      (
        ∃ c : Fin n,
          c ∈ retainedInactive C u ∧
          flipBoolWordAt word c ∈ retainedCompletionWords C u ∧
          flipBoolWordAt word c ∉ retainedCompletionWords C v ∧
          (
            (∀ w : V,
              flipBoolWordAt word c ∈ retainedCompletionWords C w →
              w = u)
            ∨
            ∃ w : V,
              w ≠ u ∧
              flipBoolWordAt word c ∈ retainedCompletionWords C w ∧
              u < w ∧ IsResidual C u w ∧
              c ∉ residualForbidden C u w
          )
      )
      ∨
      (
        ∃ c : Fin n,
          c ∈ retainedInactive C v ∧
          flipBoolWordAt word c ∈ retainedCompletionWords C v ∧
          flipBoolWordAt word c ∉ retainedCompletionWords C u ∧
          (
            (∀ w : V,
              flipBoolWordAt word c ∈ retainedCompletionWords C w →
              w = v)
            ∨
            ∃ w : V,
              w ≠ v ∧
              flipBoolWordAt word c ∈ retainedCompletionWords C w ∧
              w < v ∧ IsResidual C w v ∧
              c ∉ residualForbidden C w v
          )
      )
    )

/-- The zero--zero terminal refined to an exact/loss blocker star. -/
def ZeroZeroExactLossBlockerStar
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (word : Fin n → Bool) : Prop :=
  ∃ u v : V,
    u < v ∧
    word ∈ retainedCompletionWords C u ∧
    word ∈ retainedCompletionWords C v ∧
    exponent u = 0 ∧
    exponent v = 0 ∧
    ∃ blocker : Fin n → V,
      Function.Injective blocker ∧
      (∀ c, blocker c ≠ u) ∧
      (∀ c, blocker c ≠ v) ∧
      (∀ c,
        flipBoolWordAt word c ∈
          retainedCompletionWords C (blocker c)) ∧
      ∀ c,
        ExactProjectedBudget C exponent (blocker c)
        ∨ blocker c ∈ projectedLossVertices C exponent

/-- Every unsafe saturated hard word has one of four explicit local outlets:
a genuine hole, one unit of strict surplus, a safe residual descent, or an
injective exact/loss blocker star. -/
theorem unsafeSaturatedSaturatedWord_recursive_outlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {word : Fin n → Bool}
    (hword :
      word ∈ unsafeSaturatedSaturatedOverlapWords C exponent) :
    (
      ∃ c : Fin n,
        flipBoolWordAt word c ∉ coveredCompletionWords C
    )
    ∨
    (
      ∃ w : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) w
    )
    ∨
    UnsafeSaturatedSafeDescent C word
    ∨
    ZeroZeroExactLossBlockerStar C exponent word := by
  have hsat :
      word ∈ saturatedSaturatedOverlapWords C exponent :=
    (Finset.mem_inter.mp hword).1
  have hsatData :=
    (mem_saturatedSaturatedOverlapWords
      C exponent word).1 hsat

  rcases
      unsafeSaturatedSaturatedWord_zero_zero_or_safe_descent
        C exponent hword
    with hzero | hdescent
  · obtain ⟨u,v,huv,huWord,hvWord,huZero,hvZero⟩ := hzero
    have huExact :
        ExactProjectedBudget C exponent u :=
      hsatData.2 u huWord
    have hvExact :
        ExactProjectedBudget C exponent v :=
      hsatData.2 v hvWord
    rcases
        zero_zero_hole_or_strict_paid_or_exact_loss_star
          C exponent hexp honeLoss
          (ne_of_lt huv) huWord hvWord
          huExact hvExact huZero hvZero
      with hhole | hpaid | hstar
    · exact Or.inl hhole
    · exact Or.inr (Or.inl hpaid)
    · right
      right
      right
      obtain ⟨blocker,hinj,hneU,hneV,hblock,hprofile⟩ := hstar
      exact ⟨u,v,huv,huWord,hvWord,huZero,hvZero,
        blocker,hinj,hneU,hneV,hblock,hprofile⟩
  · exact Or.inr (Or.inr (Or.inl hdescent))

#print axioms unsafeSaturatedSaturatedWord_recursive_outlet

end OrderedEdgeColoring
end JSP000404Research
