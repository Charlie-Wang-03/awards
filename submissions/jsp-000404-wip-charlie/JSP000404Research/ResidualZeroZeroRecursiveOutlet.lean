import JSP000404Research.ResidualUnsafeZeroZeroBlockerStar
import JSP000404Research.ResidualLargeBlockerProfile
import JSP000404Research.WeightedProfileRepair
import Mathlib.Tactic

/-!
# Recursive outlet for a zero--zero duplicated full code

A zero--zero exact overlap carrier has one source hard word.  Every retained
coordinate gives a one-bit neighbour.

If one neighbour is a global hole, the hard word is immediately discharged.
Otherwise the n neighbours admit n distinct blocker vertices, all outside the
two carrier endpoints.

Classify each blocker by the projected profile trichotomy.

* strict blocker:
    exponent(w) < projectedFree(w), hence one full surplus layer exists and
    dyadicProfileSurplus(w) >= 1.  This single surplus token pays the zero--zero
    hard word.

* exact blocker:
    re-enters the saturated hard state.

* projected-loss blocker:
    re-enters the loss hard state.

Therefore, if no hole and no strict blocker exist, the zero--zero terminal
forces an injective Fin n-family of distinct exact/loss descendants.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem one_le_surplus_of_projected_strict
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {w : V}
    (hstrict : exponent w < projectedFree C w) :
    1 ≤ dyadicProfileSurplus exponent (projectedFree C) w := by
  have hcredit :=
    target_weight_le_dyadicProfileSurplus_of_one_surplus
      exponent (projectedFree C) w
      (by omega)
  have hone : 1 ≤ 2 ^ exponent w := by
    exact Nat.one_le_pow _ _
  exact hone.trans hcredit

theorem zero_zero_hole_or_injective_profile_blockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V} {base : Fin n → Bool}
    (huv : u ≠ v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huZero : exponent u = 0)
    (hvZero : exponent v = 0) :
    (
      ∃ c : Fin n,
        flipBoolWordAt base c ∉ coveredCompletionWords C
    )
    ∨
    (
      ∃ blocker : Fin n → V,
        Function.Injective blocker ∧
        (∀ c, blocker c ≠ u) ∧
        (∀ c, blocker c ≠ v) ∧
        (∀ c,
          flipBoolWordAt base c ∈
            retainedCompletionWords C (blocker c)) ∧
        ∀ c,
          (
            1 ≤ dyadicProfileSurplus
              exponent (projectedFree C) (blocker c)
          )
          ∨ ExactProjectedBudget C exponent (blocker c)
          ∨ blocker c ∈ projectedLossVertices C exponent
    ) := by
  classical
  have huFull :=
    retainedActive_eq_univ_of_exactProjectedBudget_zero
      C exponent huSat huZero
  have hvFull :=
    retainedActive_eq_univ_of_exactProjectedBudget_zero
      C exponent hvSat hvZero
  by_cases hhole :
      ∃ c : Fin n,
        flipBoolWordAt base c ∉ coveredCompletionWords C
  · exact Or.inl hhole
  · right
    push_neg at hhole
    have hcovered :
        ∀ c : Fin n,
          ∃ w : V,
            flipBoolWordAt base c ∈
              retainedCompletionWords C w := by
      intro c
      have hcov := hhole c
      have hnonempty :=
        (mem_coveredCompletionWords C
          (flipBoolWordAt base c)).1 hcov
      obtain ⟨w,hw⟩ := hnonempty
      exact ⟨w,(mem_completionFibre C _ w).1 hw⟩
    obtain ⟨blocker,hinj,hneU,hneV,hblock⟩ :=
      exists_injective_zero_zero_oneFlip_blockers
        C huv huBase hvBase huFull hvFull hcovered
    refine ⟨blocker,hinj,hneU,hneV,hblock,?_⟩
    intro c
    rcases projectedProfile_strict_exact_or_loss
        C exponent hexp honeLoss (blocker c)
      with hstrict | hexact | hloss
    · exact Or.inl
        (one_le_surplus_of_projected_strict
          C exponent hstrict)
    · exact Or.inr (Or.inl hexact)
    · exact Or.inr (Or.inr hloss)

theorem zero_zero_hole_or_strict_paid_or_exact_loss_star
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V} {base : Fin n → Bool}
    (huv : u ≠ v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huZero : exponent u = 0)
    (hvZero : exponent v = 0) :
    (
      ∃ c : Fin n,
        flipBoolWordAt base c ∉ coveredCompletionWords C
    )
    ∨
    (
      ∃ w : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) w
    )
    ∨
    (
      ∃ blocker : Fin n → V,
        Function.Injective blocker ∧
        (∀ c, blocker c ≠ u) ∧
        (∀ c, blocker c ≠ v) ∧
        (∀ c,
          flipBoolWordAt base c ∈
            retainedCompletionWords C (blocker c)) ∧
        ∀ c,
          ExactProjectedBudget C exponent (blocker c)
          ∨ blocker c ∈ projectedLossVertices C exponent
    ) := by
  rcases zero_zero_hole_or_injective_profile_blockers
      C exponent hexp honeLoss
      huv huBase hvBase huSat hvSat huZero hvZero
    with hhole | hstar
  · exact Or.inl hhole
  · obtain ⟨blocker,hinj,hneU,hneV,hblock,hprofile⟩ := hstar
    by_cases hstrictPaid :
        ∃ c : Fin n,
          1 ≤ dyadicProfileSurplus
            exponent (projectedFree C) (blocker c)
    · right
      left
      obtain ⟨c,hc⟩ := hstrictPaid
      exact ⟨blocker c,hc⟩
    · right
      right
      push_neg at hstrictPaid
      refine ⟨blocker,hinj,hneU,hneV,hblock,?_⟩
      intro c
      rcases hprofile c with hsur | hexact | hloss
      · exact False.elim (hstrictPaid c hsur)
      · exact Or.inl hexact
      · exact Or.inr hloss

#print axioms one_le_surplus_of_projected_strict
#print axioms zero_zero_hole_or_injective_profile_blockers
#print axioms zero_zero_hole_or_strict_paid_or_exact_loss_star

end OrderedEdgeColoring
end JSP000404Research
