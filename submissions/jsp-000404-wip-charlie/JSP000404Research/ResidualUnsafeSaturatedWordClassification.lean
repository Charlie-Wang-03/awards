import JSP000404Research.ResidualUnsafeSymmetricFlipDescent
import JSP000404Research.ResidualSaturatedSafeUnsafeSplit
import Mathlib.Tactic

/-!
# Word-level classification of the unsafe saturated remainder

Every unsafe saturated--saturated hard word has a unique unsafe carrier u<v.
The symmetric flip-descent theorem now shows a sharp alternative:

* both endpoint exponents are zero; or
* the word admits a one-step displacement which is singly covered at one
  endpoint or produces a new residual overlap with an explicit safe retained
  coordinate.

Thus the nonzero unsafe remainder is no longer a terminal obstruction for an
augmenting argument.  The only terminal unsafe carrier type left is zero--zero.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem unsafeSaturatedSaturatedWord_zero_zero_or_safe_descent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {word : Fin n → Bool}
    (hword :
      word ∈ unsafeSaturatedSaturatedOverlapWords C exponent) :
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
  have hsat :
      word ∈ saturatedSaturatedOverlapWords C exponent :=
    (Finset.mem_inter.mp hword).1
  have hunsafeWord :
      word ∈ unsafeOverlapWords C :=
    (Finset.mem_inter.mp hword).2
  have hunsafeWord' :
      word ∈ (unsafeOverlapCarrierPairs C).biUnion
        (pairOverlapWords C) := by
    simpa [unsafeOverlapWords] using hunsafeWord
  obtain ⟨e, heUnsafe, heWord⟩ :=
    Finset.mem_biUnion.mp hunsafeWord'
  have heData :=
    (mem_unsafeOverlapCarrierPairs C e.1 e.2).1 heUnsafe
  have heParts := Finset.mem_inter.mp heWord
  have hsatData :=
    (mem_saturatedSaturatedOverlapWords
      C exponent word).1 hsat
  have huExact :
      ExactProjectedBudget C exponent e.1 :=
    hsatData.2 e.1 heParts.1
  have hvExact :
      ExactProjectedBudget C exponent e.2 :=
    hsatData.2 e.2 heParts.2
  by_cases hu0 : exponent e.1 = 0
  · by_cases hv0 : exponent e.2 = 0
    · left
      exact ⟨e.1, e.2, heData.1,
        heParts.1, heParts.2, hu0, hv0⟩
    · right
      have hvPos : 1 ≤ exponent e.2 := by omega
      have hdescent :=
        unsafe_exact_overlap_nonzero_endpoint_has_safe_descent
          C exponent heData.1 heData.2.1
          heParts.1 heParts.2 huExact hvExact
          (Or.inr hvPos)
      exact ⟨e.1, e.2, heData.1,
        heParts.1, heParts.2, hdescent⟩
  · right
    have huPos : 1 ≤ exponent e.1 := by omega
    have hdescent :=
      unsafe_exact_overlap_nonzero_endpoint_has_safe_descent
        C exponent heData.1 heData.2.1
        heParts.1 heParts.2 huExact hvExact
        (Or.inl huPos)
    exact ⟨e.1, e.2, heData.1,
      heParts.1, heParts.2, hdescent⟩

#print axioms unsafeSaturatedSaturatedWord_zero_zero_or_safe_descent

end OrderedEdgeColoring
end JSP000404Research
