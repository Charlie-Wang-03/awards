import JSP000404Research.ProjectionLossAugmentingTransition
import JSP000404Research.ResidualLargeBlockerProfile
import JSP000404Research.WeightedProfileRepair
import Mathlib.Tactic

/-!
# Recursive outlet for one projected-loss hard word

Let v be a projected-loss vertex, x in its completion cube, and c active at v.
The translated word y = flip_c(x) leaves Q_v.

There are two possibilities.

* y is a genuine Boolean hole.
* y is covered by one or two blocker vertices, all different from v.

Classify those blockers by the one-layer projected profile. If any blocker is
strict, its pointwise dyadic surplus is at least one and therefore pays this
single hard word. Otherwise every blocker in the completion fibre of y is
either exact projected budget or projected loss.

Thus each projected-loss hard word enters exactly the same recursive hard-state
alphabet as the saturated collision outlet.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projected_strict_surplus_at_least_one
    {V : Type*}
    (exponent projectedFree : V → ℕ)
    {w : V}
    (hstrict : exponent w < projectedFree w) :
    1 ≤ dyadicProfileSurplus exponent projectedFree w := by
  have hstep : exponent w + 1 ≤ projectedFree w := by
    omega
  have hcredit :=
    target_weight_le_dyadicProfileSurplus_of_one_surplus
      exponent projectedFree w hstep
  have hone : 1 ≤ 2 ^ exponent w := by
    exact Nat.one_le_pow _ _ (by decide : 0 < (2 : ℕ))
  exact hone.trans hcredit

theorem projectedLoss_word_hole_or_strict_paid_or_exact_loss_fibre
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
    {c : Fin n}
    (hc : c ∈ retainedActive C v) :
    let y := flipBoolWordAt word c
    y ∉ coveredCompletionWords C
    ∨
    (
      ∃ w : V,
        y ∈ retainedCompletionWords C w ∧
        1 ≤ dyadicProfileSurplus exponent (projectedFree C) w
    )
    ∨
    (
      (completionFibre C y).Nonempty ∧
      (completionFibre C y).card ≤ 2 ∧
      (∀ w : V,
        w ∈ completionFibre C y →
        w ≠ v ∧
        (ExactProjectedBudget C exponent w
          ∨ w ∈ projectedLossVertices C exponent))
    ) := by
  classical
  dsimp
  by_cases hhole :
      flipBoolWordAt word c ∉ coveredCompletionWords C
  · exact Or.inl hhole
  · right
    have hcovered :
        flipBoolWordAt word c ∈ coveredCompletionWords C := by
      exact not_not.mp hhole
    have hnonempty :
        (completionFibre C (flipBoolWordAt word c)).Nonempty :=
      (mem_coveredCompletionWords C
        (flipBoolWordAt word c)).1 hcovered
    by_cases hstrictBlocker :
        ∃ w : V,
          w ∈ completionFibre C (flipBoolWordAt word c) ∧
          exponent w < projectedFree C w
    · left
      obtain ⟨w,hwFibre,hwStrict⟩ := hstrictBlocker
      exact ⟨w,
        (mem_completionFibre
          C (flipBoolWordAt word c) w).1 hwFibre,
        projected_strict_surplus_at_least_one
          exponent (projectedFree C) hwStrict⟩
    · right
      refine ⟨hnonempty,
        completionFibre_card_le_two C (flipBoolWordAt word c),?_⟩
      intro w hwFibre
      have hwMem :
          flipBoolWordAt word c ∈ retainedCompletionWords C w :=
        (mem_completionFibre
          C (flipBoolWordAt word c) w).1 hwFibre
      have hwNe : w ≠ v := by
        intro h
        subst w
        exact (flip_active_not_mem_completion C hword hc) hwMem
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

#print axioms projected_strict_surplus_at_least_one
#print axioms projectedLoss_word_hole_or_strict_paid_or_exact_loss_fibre

end OrderedEdgeColoring
end JSP000404Research
