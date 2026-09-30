import JSP000404Research.ResidualUnsafeSaturatedWordClassification
import JSP000404Research.ResidualSaturatedSafeUnsafeSplit
import Mathlib.Tactic

/-!
# Unified transition classification for saturated--saturated hard words

Every saturated--saturated overlap word has a unique residual carrier u<v.
There are only three structural possibilities relevant to the global
augmenting argument.

1. The carrier is already safe: some retained coordinate lies outside
   residualForbidden(u,v).

2. The carrier is unsafe and both endpoint exponents are zero.  This is the
   terminal duplicated-full-code obstruction.

3. The carrier is unsafe and nonzero.  Existing symmetric flip descent moves
   the word in one step to either a single anchored completion word or a new
   residual overlap carrying an explicit safe coordinate.

Thus every nonterminal saturated--saturated hard word enters the same safe
transition machine after at most one preliminary displacement.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem saturatedSaturatedWord_safe_or_zero_zero_or_safe_descent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {word : Fin n → Bool}
    (hword : word ∈ saturatedSaturatedOverlapWords C exponent) :
    (
      ∃ u v : V,
        u < v ∧
        IsResidual C u v ∧
        word ∈ retainedCompletionWords C u ∧
        word ∈ retainedCompletionWords C v ∧
        ExactProjectedBudget C exponent u ∧
        ExactProjectedBudget C exponent v ∧
        ∃ c : Fin n, c ∉ residualForbidden C u v
    )
    ∨
    (
      ∃ u v : V,
        u < v ∧
        word ∈ retainedCompletionWords C u ∧
        word ∈ retainedCompletionWords C v ∧
        exponent u = 0 ∧ exponent v = 0
    )
    ∨
    (
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
    ) := by
  classical
  have hsatData :=
    (mem_saturatedSaturatedOverlapWords
      C exponent word).1 hword
  obtain ⟨u,v,huv,hres,huWord,hvWord,huniq⟩ :=
    exists_ordered_residual_pair_of_overlapWord C hsatData.1
  have huExact : ExactProjectedBudget C exponent u :=
    hsatData.2 u huWord
  have hvExact : ExactProjectedBudget C exponent v :=
    hsatData.2 v hvWord
  by_cases hsafe : ∃ c : Fin n, c ∉ residualForbidden C u v
  · left
    exact ⟨u,v,huv,hres,huWord,hvWord,huExact,hvExact,hsafe⟩
  · right
    have hpair :
        (u,v) ∈ unsafeOverlapCarrierPairs C := by
      apply (mem_unsafeOverlapCarrierPairs C u v).2
      exact ⟨huv,hsafe,⟨word,huWord,hvWord⟩⟩
    have hunsafeWord :
        word ∈ unsafeOverlapWords C := by
      unfold unsafeOverlapWords
      apply Finset.mem_biUnion.mpr
      refine ⟨(u,v),hpair,?_⟩
      exact Finset.mem_inter.mpr ⟨huWord,hvWord⟩
    have hunsafeSat :
        word ∈ unsafeSaturatedSaturatedOverlapWords C exponent := by
      exact Finset.mem_inter.mpr ⟨hword,hunsafeWord⟩
    rcases
      unsafeSaturatedSaturatedWord_zero_zero_or_safe_descent
        C exponent hunsafeSat
      with hzero | hdescent
    · exact Or.inl hzero
    · exact Or.inr hdescent

#print axioms saturatedSaturatedWord_safe_or_zero_zero_or_safe_descent

end OrderedEdgeColoring
end JSP000404Research
