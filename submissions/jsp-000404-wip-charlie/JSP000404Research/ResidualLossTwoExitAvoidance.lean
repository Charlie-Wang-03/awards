import JSP000404Research.ResidualSingleFibreBranching
import JSP000404Research.ResidualLossWords
import Mathlib.Tactic

/-!
# A fixed blocker cannot obstruct both exits of a loss word

Let x belong to the completion cube of a projected-loss vertex v.  Such a word
is singly covered by v.  If c and d are distinct active coordinates at v, the
two one-bit translates flip_c(x) and flip_d(x) have disjoint completion
fibres.

Equivalently, for every fixed blocker vertex w, at most one of the two
translated words can lie in Q_w.

This is the pointwise form needed for extreme-loss routing: the global top may
block one outgoing exit from the bottom loss vertex, but it cannot block two
distinct active exits of the same loss word; dually for the global bottom.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedLoss_fixed_blocker_cannot_block_two_flips
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v)
    {c d : Fin n}
    (hc : c ∈ retainedActive C v)
    (hd : d ∈ retainedActive C v)
    (hcd : c ≠ d)
    (w : V) :
    ¬ (
      flipBoolWordAt word c ∈ retainedCompletionWords C w ∧
      flipBoolWordAt word d ∈ retainedCompletionWords C w) := by
  have hsingle :=
    projectedLoss_word_is_singleCompletionWord
      C exponent hexp honeLoss hvLoss hword
  have hdisj :=
    two_single_flips_have_disjoint_blocker_fibres
      C hsingle hc hd hcd
  intro hboth
  have hcF :
      w ∈ completionFibre C (flipBoolWordAt word c) :=
    (mem_completionFibre C _ w).2 hboth.1
  have hdF :
      w ∈ completionFibre C (flipBoolWordAt word d) :=
    (mem_completionFibre C _ w).2 hboth.2
  exact Finset.disjoint_left.mp hdisj hcF hdF

theorem projectedLoss_two_flips_avoid_fixed_blocker
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v)
    {c d : Fin n}
    (hc : c ∈ retainedActive C v)
    (hd : d ∈ retainedActive C v)
    (hcd : c ≠ d)
    (w : V) :
    flipBoolWordAt word c ∉ retainedCompletionWords C w
    ∨
    flipBoolWordAt word d ∉ retainedCompletionWords C w := by
  by_contra h
  push_neg at h
  exact projectedLoss_fixed_blocker_cannot_block_two_flips
    C exponent hexp honeLoss hvLoss hword hc hd hcd w
    ⟨h.1,h.2⟩

theorem projectedLoss_two_flips_one_avoids_owner_and_fixed_blocker
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v)
    {c d : Fin n}
    (hc : c ∈ retainedActive C v)
    (hd : d ∈ retainedActive C v)
    (hcd : c ≠ d)
    (w : V) :
    ∃ e : Fin n,
      (e = c ∨ e = d) ∧
      flipBoolWordAt word e ∉ retainedCompletionWords C v ∧
      flipBoolWordAt word e ∉ retainedCompletionWords C w := by
  rcases projectedLoss_two_flips_avoid_fixed_blocker
      C exponent hexp honeLoss hvLoss hword hc hd hcd w
    with hcAvoid | hdAvoid
  · exact ⟨c,Or.inl rfl,
      flip_active_not_mem_completion C hword hc,
      hcAvoid⟩
  · exact ⟨d,Or.inr rfl,
      flip_active_not_mem_completion C hword hd,
      hdAvoid⟩

#print axioms projectedLoss_fixed_blocker_cannot_block_two_flips
#print axioms projectedLoss_two_flips_avoid_fixed_blocker
#print axioms projectedLoss_two_flips_one_avoids_owner_and_fixed_blocker

end OrderedEdgeColoring
end JSP000404Research
