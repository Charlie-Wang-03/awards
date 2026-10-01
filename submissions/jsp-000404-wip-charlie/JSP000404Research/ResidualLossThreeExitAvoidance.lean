import JSP000404Research.ResidualLossTwoExitAvoidance
import JSP000404Research.ResidualProjectionLoss
import Mathlib.Tactic

/-!
# Three-exit avoidance for second-layer projected loss

The two-exit lemma already shows that a fixed blocker completion cube can
contain at most one active one-coordinate translate of a singly covered
projected-loss word.

This file records the next layer needed by the enlarged-candidate Hall route.

* If a projected-loss vertex has exponent n-2, then its retained active
  palette has exactly three coordinates.
* Given three distinct active coordinates c,d,e, and two fixed blockers w₁,w₂,
  at least one of the three flips avoids the owner and both blockers.

Thus a second-layer loss has a genuine three-exit local outlet against any two
prescribed completion blockers.  The remaining global work is to turn these
local outlets into a compatible Hall/augmenting routing.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedLoss_secondLayer_retainedActive_card_eq_three
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2) :
    (retainedActive C v).card = 3 := by
  have hloss :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  have hcardLe :
      (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  unfold projectedFree at hloss
  omega

theorem projectedLoss_three_flips_one_avoids_two_fixed_blockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v)
    {c d e : Fin n}
    (hc : c ∈ retainedActive C v)
    (hd : d ∈ retainedActive C v)
    (he : e ∈ retainedActive C v)
    (hcd : c ≠ d)
    (hce : c ≠ e)
    (hde : d ≠ e)
    (w₁ w₂ : V) :
    ∃ q : Fin n,
      (q = c ∨ q = d ∨ q = e) ∧
      flipBoolWordAt word q ∉ retainedCompletionWords C v ∧
      flipBoolWordAt word q ∉ retainedCompletionWords C w₁ ∧
      flipBoolWordAt word q ∉ retainedCompletionWords C w₂ := by
  classical
  let fc := flipBoolWordAt word c
  let fd := flipBoolWordAt word d
  let fe := flipBoolWordAt word e

  have hcOwner :
      fc ∉ retainedCompletionWords C v := by
    dsimp [fc]
    exact flip_active_not_mem_completion C hword hc
  have hdOwner :
      fd ∉ retainedCompletionWords C v := by
    dsimp [fd]
    exact flip_active_not_mem_completion C hword hd
  have heOwner :
      fe ∉ retainedCompletionWords C v := by
    dsimp [fe]
    exact flip_active_not_mem_completion C hword he

  by_cases hc1 : fc ∈ retainedCompletionWords C w₁
  · have hd1 : fd ∉ retainedCompletionWords C w₁ := by
      intro hd1
      exact projectedLoss_fixed_blocker_cannot_block_two_flips
        C exponent hexp honeLoss hvLoss hword hc hd hcd w₁
        ⟨hc1,hd1⟩
    have he1 : fe ∉ retainedCompletionWords C w₁ := by
      intro he1
      exact projectedLoss_fixed_blocker_cannot_block_two_flips
        C exponent hexp honeLoss hvLoss hword hc he hce w₁
        ⟨hc1,he1⟩
    by_cases hd2 : fd ∈ retainedCompletionWords C w₂
    · have he2 : fe ∉ retainedCompletionWords C w₂ := by
        intro he2
        exact projectedLoss_fixed_blocker_cannot_block_two_flips
          C exponent hexp honeLoss hvLoss hword hd he hde w₂
          ⟨hd2,he2⟩
      refine ⟨e,Or.inr (Or.inr rfl),heOwner,?_,?_⟩
      · simpa [fe] using he1
      · simpa [fe] using he2
    · refine ⟨d,Or.inr (Or.inl rfl),hdOwner,?_,?_⟩
      · simpa [fd] using hd1
      · simpa [fd] using hd2
  · by_cases hc2 : fc ∈ retainedCompletionWords C w₂
    · have hd2 : fd ∉ retainedCompletionWords C w₂ := by
        intro hd2
        exact projectedLoss_fixed_blocker_cannot_block_two_flips
          C exponent hexp honeLoss hvLoss hword hc hd hcd w₂
          ⟨hc2,hd2⟩
      by_cases hd1 : fd ∈ retainedCompletionWords C w₁
      · have he1 : fe ∉ retainedCompletionWords C w₁ := by
          intro he1
          exact projectedLoss_fixed_blocker_cannot_block_two_flips
            C exponent hexp honeLoss hvLoss hword hd he hde w₁
            ⟨hd1,he1⟩
        have he2 : fe ∉ retainedCompletionWords C w₂ := by
          intro he2
          exact projectedLoss_fixed_blocker_cannot_block_two_flips
            C exponent hexp honeLoss hvLoss hword hc he hce w₂
            ⟨hc2,he2⟩
        refine ⟨e,Or.inr (Or.inr rfl),heOwner,?_,?_⟩
        · simpa [fe] using he1
        · simpa [fe] using he2
      · refine ⟨d,Or.inr (Or.inl rfl),hdOwner,?_,?_⟩
        · simpa [fd] using hd1
        · simpa [fd] using hd2
    · refine ⟨c,Or.inl rfl,hcOwner,?_,?_⟩
      · simpa [fc] using hc1
      · simpa [fc] using hc2

#print axioms projectedLoss_secondLayer_retainedActive_card_eq_three
#print axioms projectedLoss_three_flips_one_avoids_two_fixed_blockers

end OrderedEdgeColoring
end JSP000404Research
