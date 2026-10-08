import JSP000404Research.ResidualLossRecursiveOutlet
import JSP000404Research.ResidualSingleFibreBranching
import Mathlib.Tactic

/-!
# Two-exit recursive outlet for one projected-loss hard word

A projected-loss completion word is singly covered by its owner.  Choose two
distinct retained-active coordinates c,d.

The two one-bit translated completion fibres are disjoint.  Therefore the
two-exit recursion has the following sharp form:

* one of the two flips is a genuine Boolean hole; or
* some blocker reached by either flip is strict and contributes at least one
  profile-surplus token, paying this one hard word; or
* both blocker fibres are nonempty, each has cardinality at most two, they are
  disjoint, and every blocker in either fibre is an exact projected-budget
  vertex or a projected-loss vertex.

Thus an unpaid loss state branches into two disjoint exact/loss descendant
fibres rather than continuing along one arbitrary blocker.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedLoss_two_exit_hole_or_paid_or_disjoint_exact_loss_fibres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v)
    {c d : Fin n}
    (hc : c ∈ retainedActive C v)
    (hd : d ∈ retainedActive C v)
    (hcd : c ≠ d) :
    (
      flipBoolWordAt word c ∉ coveredCompletionWords C
    )
    ∨
    (
      flipBoolWordAt word d ∉ coveredCompletionWords C
    )
    ∨
    (
      ∃ w : V,
        (
          w ∈ completionFibre C (flipBoolWordAt word c)
          ∨
          w ∈ completionFibre C (flipBoolWordAt word d)
        ) ∧
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) w
    )
    ∨
    (
      (completionFibre C (flipBoolWordAt word c)).Nonempty ∧
      (completionFibre C (flipBoolWordAt word d)).Nonempty ∧
      (completionFibre C (flipBoolWordAt word c)).card ≤ 2 ∧
      (completionFibre C (flipBoolWordAt word d)).card ≤ 2 ∧
      Disjoint
        (completionFibre C (flipBoolWordAt word c))
        (completionFibre C (flipBoolWordAt word d)) ∧
      ∀ w : V,
        (
          w ∈ completionFibre C (flipBoolWordAt word c)
          ∨
          w ∈ completionFibre C (flipBoolWordAt word d)
        ) →
        w ≠ v ∧
        (
          ExactProjectedBudget C exponent w
          ∨
          w ∈ projectedLossVertices C exponent
        )
    ) := by
  classical
  have hsingle :=
    projectedLoss_word_is_singleCompletionWord
      C exponent hexp honeLoss hvLoss hword
  by_cases hcHole :
      flipBoolWordAt word c ∉ coveredCompletionWords C
  · exact Or.inl hcHole
  · right
    by_cases hdHole :
        flipBoolWordAt word d ∉ coveredCompletionWords C
    · exact Or.inl hdHole
    · right
      have hcCovered :
          flipBoolWordAt word c ∈ coveredCompletionWords C := by
        exact not_not.mp hcHole
      have hdCovered :
          flipBoolWordAt word d ∈ coveredCompletionWords C := by
        exact not_not.mp hdHole
      have hcNonempty :
          (completionFibre C (flipBoolWordAt word c)).Nonempty :=
        (mem_coveredCompletionWords C
          (flipBoolWordAt word c)).1 hcCovered
      have hdNonempty :
          (completionFibre C (flipBoolWordAt word d)).Nonempty :=
        (mem_coveredCompletionWords C
          (flipBoolWordAt word d)).1 hdCovered

      by_cases hstrictBlocker :
          ∃ w : V,
            (
              w ∈ completionFibre C (flipBoolWordAt word c)
              ∨
              w ∈ completionFibre C (flipBoolWordAt word d)
            ) ∧
            exponent w < projectedFree C w
      · left
        obtain ⟨w,hwFibre,hwStrict⟩ := hstrictBlocker
        exact ⟨w,hwFibre,
          projected_strict_surplus_at_least_one
            exponent (projectedFree C) hwStrict⟩
      · right
        refine ⟨hcNonempty,hdNonempty,
          completionFibre_card_le_two
            C (flipBoolWordAt word c),
          completionFibre_card_le_two
            C (flipBoolWordAt word d),
          two_single_flips_have_disjoint_blocker_fibres
            C hsingle hc hd hcd,
          ?_⟩
        intro w hwFibre
        have hwNe : w ≠ v := by
          intro h
          subst w
          rcases hwFibre with hwc | hwd
          · have hwcMem :=
              (mem_completionFibre
                C (flipBoolWordAt word c) v).1 hwc
            exact
              (flip_active_not_mem_completion
                C hword hc) hwcMem
          · have hwdMem :=
              (mem_completionFibre
                C (flipBoolWordAt word d) v).1 hwd
            exact
              (flip_active_not_mem_completion
                C hword hd) hwdMem
        have hnotStrict :
            ¬ exponent w < projectedFree C w := by
          intro hs
          exact hstrictBlocker ⟨w,hwFibre,hs⟩
        rcases projectedProfile_strict_exact_or_loss
            C exponent hexp honeLoss w
          with hs | hexact | hloss
        · exact False.elim (hnotStrict hs)
        · exact ⟨hwNe,Or.inl hexact⟩
        · exact ⟨hwNe,Or.inr hloss⟩

#print axioms projectedLoss_two_exit_hole_or_paid_or_disjoint_exact_loss_fibres

end OrderedEdgeColoring
end JSP000404Research
