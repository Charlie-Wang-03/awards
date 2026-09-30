import JSP000404Research.ResidualPairLocalFlip
import JSP000404Research.ResidualAugmentingState
import Mathlib.Tactic

/-!
# Saturated pair-local injection as a global structural transition

The explicit saturated-pair map already injects the entire overlap cube into
the complement of its two endpoint completion cubes.  Globally those local
holes need not be uncovered: another completion cube may occupy them.

This file records the precise structural consequence.  There is one injective
one- or two-bit map f for the whole carrier overlap cube, and for every source
word its image is either

* a genuine global Boolean hole;
* singly covered by a vertex different from both original endpoints; or
* doubly covered by a residual pair whose two endpoints are both different
  from the original carrier endpoints.

Thus a saturated carrier has a uniform injective exit into states supported
strictly outside that carrier.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exists_saturated_pair_injective_structural_exit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (huv : u < v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huLt : exponent u < n)
    (hvLt : exponent v < n) :
    ∃ f :
      {word : Fin n → Bool //
        word ∈ retainedCompletionWords C u ∩
          retainedCompletionWords C v} →
      {word : Fin n → Bool // word ∈ pairLocalHoles C u v},
      Function.Injective f ∧
      (
        (∃ c : Fin n,
          ∀ word, (f word).1 = flipBoolWordAt word.1 c)
        ∨
        (∃ c d : Fin n, c ≠ d ∧
          ∀ word,
            (f word).1 =
              flipBoolWordAt (flipBoolWordAt word.1 c) d)
      ) ∧
      ∀ word,
        let y := (f word).1
        y ∉ coveredCompletionWords C
        ∨
        (∃ w : V,
          IsSingleCompletionWord C w y ∧
          w ≠ u ∧ w ≠ v)
        ∨
        (∃ a b : V,
          a < b ∧
          IsResidual C a b ∧
          y ∈ retainedCompletionWords C a ∧
          y ∈ retainedCompletionWords C b ∧
          a ≠ u ∧ a ≠ v ∧
          b ≠ u ∧ b ≠ v) := by
  classical
  obtain ⟨f,hf,hshape⟩ :=
    exists_saturated_pair_explicit_flip_to_local_holes
      C exponent huSat hvSat huLt hvLt
  refine ⟨f,hf,hshape,?_⟩
  intro word
  dsimp
  have hlocal := (f word).2
  have hnotUnion :
      (f word).1 ∉
        retainedCompletionWords C u ∪ retainedCompletionWords C v :=
    (Finset.mem_sdiff.mp hlocal).2
  have hnotU :
      (f word).1 ∉ retainedCompletionWords C u := by
    intro hu
    exact hnotUnion (Finset.mem_union_left _ hu)
  have hnotV :
      (f word).1 ∉ retainedCompletionWords C v := by
    intro hv
    exact hnotUnion (Finset.mem_union_right _ hv)
  rcases completionWord_structural_trichotomy C (f word).1
    with hhole | hsingle | hoverlap
  · exact Or.inl hhole
  · right
    left
    obtain ⟨w,hwSingle⟩ := hsingle
    have hwu : w ≠ u := by
      intro h
      subst w
      exact hnotU hwSingle.1
    have hwv : w ≠ v := by
      intro h
      subst w
      exact hnotV hwSingle.1
    exact ⟨w,hwSingle,hwu,hwv⟩
  · right
    right
    obtain ⟨a,b,hab,hres,ha,hb⟩ := hoverlap
    have hau : a ≠ u := by
      intro h; subst a; exact hnotU ha
    have hav : a ≠ v := by
      intro h; subst a; exact hnotV ha
    have hbu : b ≠ u := by
      intro h; subst b; exact hnotU hb
    have hbv : b ≠ v := by
      intro h; subst b; exact hnotV hb
    exact ⟨a,b,hab,hres,ha,hb,hau,hav,hbu,hbv⟩

#print axioms exists_saturated_pair_injective_structural_exit

end OrderedEdgeColoring
end JSP000404Research
