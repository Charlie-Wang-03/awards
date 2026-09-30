import JSP000404Research.ResidualPairLocalFlip
import JSP000404Research.ResidualTranslatedOverlapCaptureDichotomy
import Mathlib.Tactic

/-!
# Saturated pair-local injection with uniform blocker collision control

For a saturated pair u,v with positive retained-active palettes, choose the same
explicit one- or two-coordinate injection used by the pair-local hole theorem.

This strengthened version retains the active-coordinate witnesses and attaches
a quantitative statement for every potential blocker w:

* either w captures at most half of the source overlap cube under that fixed
  local map;
* or Q_w has cardinality at least the entire source overlap cube.

The map is fixed once for the pair; the blocker alternative is uniform over
all w.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exists_saturated_pair_injection_with_blocker_control
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huLt : exponent u < n)
    (hvLt : exponent v < n) :
    ∃ f :
      {word : Fin n → Bool //
        word ∈ retainedCompletionWords C u ∩
          retainedCompletionWords C v} →
      {word : Fin n → Bool //
        word ∈ pairLocalHoles C u v},
      Function.Injective f ∧
      (
        (
          ∃ c : Fin n,
            c ∈ retainedActive C u ∧
            c ∈ retainedActive C v ∧
            (∀ word,
              (f word).1 = flipBoolWordAt word.1 c) ∧
            ∀ w : V,
              2 * (oneFlipCapturedSourceWords C u v w c).card ≤
                  (retainedCompletionWords C u ∩
                    retainedCompletionWords C v).card
              ∨
              (retainedCompletionWords C u ∩
                retainedCompletionWords C v).card ≤
                  (retainedCompletionWords C w).card
        )
        ∨
        (
          ∃ c d : Fin n,
            c ≠ d ∧
            c ∈ retainedActive C u ∧
            d ∈ retainedActive C v ∧
            (∀ word,
              (f word).1 =
                flipBoolWordAt
                  (flipBoolWordAt word.1 c) d) ∧
            ∀ w : V,
              2 * (twoFlipCapturedSourceWords C u v w c d).card ≤
                  (retainedCompletionWords C u ∩
                    retainedCompletionWords C v).card
              ∨
              (retainedCompletionWords C u ∩
                retainedCompletionWords C v).card ≤
                  (retainedCompletionWords C w).card
        )
      ) := by
  classical
  let Au := retainedActive C u
  let Av := retainedActive C v
  by_cases hcommon : (Au ∩ Av).Nonempty
  · obtain ⟨c,hc⟩ := hcommon
    have hcu : c ∈ retainedActive C u :=
      (Finset.mem_inter.mp hc).1
    have hcv : c ∈ retainedActive C v :=
      (Finset.mem_inter.mp hc).2
    let f :
        {word : Fin n → Bool //
          word ∈ retainedCompletionWords C u ∩
            retainedCompletionWords C v} →
        {word : Fin n → Bool //
          word ∈ pairLocalHoles C u v} :=
      fun word => ⟨flipBoolWordAt word.1 c, by
        have hparts := Finset.mem_inter.mp word.2
        simp only [pairLocalHoles, Finset.mem_sdiff,
          Finset.mem_univ, true_and]
        rw [Finset.mem_union]
        push_neg
        exact ⟨
          flip_active_not_mem_completion C hparts.1 hcu,
          flip_active_not_mem_completion C hparts.2 hcv⟩⟩
    refine ⟨f,?_,Or.inl ?_⟩
    · intro x y hxy
      apply Subtype.ext
      apply flipBoolWordAt_injective c
      exact congrArg Subtype.val hxy
    · refine ⟨c,hcu,hcv,?_,?_⟩
      · intro word
        rfl
      · intro w
        exact oneFlip_blocker_halfCapture_or_fullCapacity
          C hcu
  · have hAuPos : Au.Nonempty := by
      have hcard :
          0 < (retainedActive C u).card := by
        unfold ExactProjectedBudget projectedFree at huSat
        have hle :
            (retainedActive C u).card ≤ n := by
          simpa using Finset.card_le_univ (retainedActive C u)
        omega
      exact Finset.card_pos.mp hcard
    have hAvPos : Av.Nonempty := by
      have hcard :
          0 < (retainedActive C v).card := by
        unfold ExactProjectedBudget projectedFree at hvSat
        have hle :
            (retainedActive C v).card ≤ n := by
          simpa using Finset.card_le_univ (retainedActive C v)
        omega
      exact Finset.card_pos.mp hcard
    obtain ⟨c,hcu⟩ := hAuPos
    obtain ⟨d,hdv⟩ := hAvPos
    have hcd : c ≠ d := by
      intro h
      subst d
      exact hcommon ⟨c,Finset.mem_inter.mpr ⟨hcu,hdv⟩⟩
    let f :
        {word : Fin n → Bool //
          word ∈ retainedCompletionWords C u ∩
            retainedCompletionWords C v} →
        {word : Fin n → Bool //
          word ∈ pairLocalHoles C u v} :=
      fun word => ⟨
        flipBoolWordAt (flipBoolWordAt word.1 c) d,
        by
          have hparts := Finset.mem_inter.mp word.2
          simp only [pairLocalHoles, Finset.mem_sdiff,
            Finset.mem_univ, true_and]
          rw [Finset.mem_union]
          push_neg
          exact ⟨
            two_flip_first_active_not_mem_completion
              C hparts.1 hcu hcd,
            two_flip_second_active_not_mem_completion
              C hparts.2 hdv hcd⟩⟩
    refine ⟨f,?_,Or.inr ?_⟩
    · intro x y hxy
      apply Subtype.ext
      apply two_flip_injective c d
      exact congrArg Subtype.val hxy
    · refine ⟨c,d,hcd,hcu,hdv,?_,?_⟩
      · intro word
        rfl
      · intro w
        exact twoFlip_blocker_halfCapture_or_fullCapacity
          C hcu hdv

#print axioms exists_saturated_pair_injection_with_blocker_control

end OrderedEdgeColoring
end JSP000404Research
