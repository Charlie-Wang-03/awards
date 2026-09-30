import JSP000404Research.ResidualSafeFlipTransition
import Mathlib.Tactic

/-!
# Safe overlaps without common inactive coordinates are deterministic

For a safe overlap pair u<v, choose any safe retained coordinate c.
ResidualOverlapFlip gives three possibilities:

* c active only at u;
* c active only at v;
* c inactive at both endpoints.

If the pair has no common inactive coordinate, the third case is impossible.
Thus every safe no-common-inactive overlap admits an anchored one-bit
displacement, and the unique-blocker transition API applies immediately.

This isolates the genuinely non-deterministic two-bit branch to overlap pairs
with a common inactive retained coordinate.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem safe_noCommonInactive_has_active_only_coordinate
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hsafe : ∃ c : Fin n, c ∉ residualForbidden C u v)
    (hnoCommon :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v) :
    ∃ c : Fin n,
      c ∉ residualForbidden C u v ∧
      ((c ∈ retainedActive C u ∧
        c ∉ retainedActive C v) ∨
       (c ∉ retainedActive C u ∧
        c ∈ retainedActive C v)) := by
  obtain ⟨c, hcSafe⟩ := hsafe
  rcases safe_overlap_flip_trichotomy
      C hu hv hcSafe with hleft | hright | hcommon
  · refine ⟨c, hcSafe, Or.inl ⟨hleft.1, ?_⟩⟩
    intro hcv
    exact safe_overlap_not_active_both
      C hu hv hcSafe ⟨hleft.1,hcv⟩
  · refine ⟨c, hcSafe, Or.inr ⟨?_, hright.1⟩⟩
    intro hcu
    exact safe_overlap_not_active_both
      C hu hv hcSafe ⟨hcu,hright.1⟩
  · exact False.elim
      (hnoCommon ⟨c, hcommon.1, hcommon.2.1⟩)

theorem safe_noCommonInactive_deterministic_transition
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huv : u < v)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hsafe : ∃ c : Fin n, c ∉ residualForbidden C u v)
    (hnoCommon :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v) :
    ∃ c : Fin n,
      c ∉ residualForbidden C u v ∧
      (
        (c ∈ retainedActive C u ∧
          ((∀ z : V,
              flipRetainedWord word c ∈ retainedCompletionWords C z →
              z = v)
           ∨
           ∃ w : V,
             w ≠ v ∧
             flipRetainedWord word c ∈ retainedCompletionWords C w ∧
             (if hvw : v < w then
                IsResidual C v w ∧
                  c ∉ residualForbidden C v w
              else
                w < v ∧ IsResidual C w v) ∧
             ∀ z : V,
               z ≠ v →
               flipRetainedWord word c ∈ retainedCompletionWords C z →
               z = w))
        ∨
        (c ∈ retainedActive C v ∧
          ((∀ z : V,
              flipRetainedWord word c ∈ retainedCompletionWords C z →
              z = u)
           ∨
           ∃ w : V,
             w ≠ u ∧
             flipRetainedWord word c ∈ retainedCompletionWords C w ∧
             (if hwu : w < u then
                IsResidual C w u ∧
                  c ∉ residualForbidden C w u
              else
                u < w ∧ IsResidual C u w) ∧
             ∀ z : V,
               z ≠ u →
               flipRetainedWord word c ∈ retainedCompletionWords C z →
               z = w)
      ) := by
  obtain ⟨c, hcSafe, hactive⟩ :=
    safe_noCommonInactive_has_active_only_coordinate
      C hu hv hsafe hnoCommon
  refine ⟨c, hcSafe, ?_⟩
  rcases hactive with hleft | hright
  · left
    refine ⟨hleft.1, ?_⟩
    exact safe_left_active_flip_single_or_unique_blocker
      C huv hu hv hcSafe hleft.1
  · right
    refine ⟨hright.2, ?_⟩
    exact safe_right_active_flip_single_or_unique_blocker
      C huv hu hv hcSafe hright.2

#print axioms safe_noCommonInactive_has_active_only_coordinate
#print axioms safe_noCommonInactive_deterministic_transition

end OrderedEdgeColoring
end JSP000404Research
