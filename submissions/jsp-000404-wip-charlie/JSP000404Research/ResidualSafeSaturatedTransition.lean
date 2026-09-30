import JSP000404Research.ResidualSaturatedGlobalTransition
import JSP000404Research.ResidualSafeDeterministicTransition
import Mathlib.Tactic

/-!
# Safe saturated carriers: common-inactive or deterministic transition

For a safe residual overlap u<v carrying a common word, there are two sharply
different possibilities.

* The endpoints have a common inactive retained coordinate.  This is the
  genuinely higher-dimensional overlap case.

* There is no common inactive coordinate.  Then the existing safe deterministic
  transition theorem supplies an active-only safe coordinate and an anchored
  one-bit transition with at most one additional blocker.

For saturated--saturated hard carriers this isolates the only non-deterministic
safe subtype to the explicit common-inactive case.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem safe_overlap_commonInactive_or_deterministic_transition
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huv : u < v)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hsafe : ∃ c : Fin n, c ∉ residualForbidden C u v) :
    (
      ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v
    )
    ∨
    (
      ∃ c : Fin n,
        c ∉ residualForbidden C u v ∧
        (
          (c ∈ retainedActive C u ∧
            (
              (∀ z : V,
                flipRetainedWord word c ∈ retainedCompletionWords C z →
                z = v)
              ∨
              ∃ w : V,
                w ≠ v ∧
                flipRetainedWord word c ∈ retainedCompletionWords C w ∧
                w < v ∧
                IsResidual C w v ∧
                c ∈ residualForbidden C w v ∧
                ∀ z : V,
                  z ≠ v →
                  flipRetainedWord word c ∈ retainedCompletionWords C z →
                  z = w
            ))
          ∨
          (c ∈ retainedActive C v ∧
            (
              (∀ z : V,
                flipRetainedWord word c ∈ retainedCompletionWords C z →
                z = u)
              ∨
              ∃ w : V,
                w ≠ u ∧
                flipRetainedWord word c ∈ retainedCompletionWords C w ∧
                u < w ∧
                IsResidual C u w ∧
                c ∈ residualForbidden C u w ∧
                ∀ z : V,
                  z ≠ u →
                  flipRetainedWord word c ∈ retainedCompletionWords C z →
                  z = w
            ))
        )
    ) := by
  by_cases hcommon :
      ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v
  · exact Or.inl hcommon
  · right
    exact safe_noCommonInactive_single_or_consumed_blocker
      C huv hu hv hsafe hcommon

theorem safe_saturatedSaturatedWord_commonInactive_or_deterministic
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {word : Fin n → Bool}
    (hword : word ∈ saturatedSaturatedOverlapWords C exponent)
    {u v : V}
    (huv : u < v)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hsafe : ∃ c : Fin n, c ∉ residualForbidden C u v) :
    ExactProjectedBudget C exponent u ∧
    ExactProjectedBudget C exponent v ∧
    (
      (
        ∃ c : Fin n,
          c ∉ retainedActive C u ∧
          c ∉ retainedActive C v
      )
      ∨
      (
        ∃ c : Fin n,
          c ∉ residualForbidden C u v ∧
          (
            (c ∈ retainedActive C u ∧
              (
                (∀ z : V,
                  flipRetainedWord word c ∈ retainedCompletionWords C z →
                  z = v)
                ∨
                ∃ w : V,
                  w ≠ v ∧
                  flipRetainedWord word c ∈ retainedCompletionWords C w ∧
                  w < v ∧
                  IsResidual C w v ∧
                  c ∈ residualForbidden C w v ∧
                  ∀ z : V,
                    z ≠ v →
                    flipRetainedWord word c ∈ retainedCompletionWords C z →
                    z = w
              ))
            ∨
            (c ∈ retainedActive C v ∧
              (
                (∀ z : V,
                  flipRetainedWord word c ∈ retainedCompletionWords C z →
                  z = u)
                ∨
                ∃ w : V,
                  w ≠ u ∧
                  flipRetainedWord word c ∈ retainedCompletionWords C w ∧
                  u < w ∧
                  IsResidual C u w ∧
                  c ∈ residualForbidden C u w ∧
                  ∀ z : V,
                    z ≠ u →
                    flipRetainedWord word c ∈ retainedCompletionWords C z →
                    z = w
              ))
          )
      )
    ) := by
  have hsat :=
    (mem_saturatedSaturatedOverlapWords
      C exponent word).1 hword
  have huExact := hsat.2 u hu
  have hvExact := hsat.2 v hv
  exact ⟨huExact,hvExact,
    safe_overlap_commonInactive_or_deterministic_transition
      C huv hu hv hsafe⟩

#print axioms safe_overlap_commonInactive_or_deterministic_transition
#print axioms safe_saturatedSaturatedWord_commonInactive_or_deterministic

end OrderedEdgeColoring
end JSP000404Research
