import JSP000404Research.ResidualActiveStarCandidate
import JSP000404Research.ResidualProjectionLoss
import Mathlib.Tactic

/-!
# Exact capacity and slack of a projected-loss active star

At a projected-loss vertex v,

  exponent(v) = projectedFree(v) + 1
              = n - card(retainedActive(v)) + 1.

Hence

  card(retainedActive(v)) = n - exponent(v) + 1.

The active-star candidate block consists of the original completion cube and
one disjoint translate for every retained-active coordinate.  Therefore

  card Star(v)
    = (n - exponent(v) + 2) * 2^(exponent(v)-1).

In the planar lower branch exponent(v) < n, so the local slack beyond the
target mass 2^exponent(v) is at least 2^(exponent(v)-1).
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedLoss_retainedActive_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent) :
    (retainedActive C v).card = n - exponent v + 1 := by
  have hloss :
      exponent v = projectedFree C v + 1 :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  unfold projectedFree at hloss
  have hactive :
      (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  omega

theorem projectedLoss_completion_card_eq_half_target
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent) :
    2 * (retainedCompletionWords C v).card =
      2 ^ exponent v := by
  have hloss :
      exponent v = projectedFree C v + 1 :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  rw [retainedCompletionWords_card, hloss, pow_succ]
  omega

theorem projectedLoss_activeStar_card_times_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent) :
    2 * (activeStarCandidateBlock C v).card =
      (n - exponent v + 2) * 2 ^ exponent v := by
  rw [activeStarCandidateBlock_card,
      projectedLoss_retainedActive_card C exponent hvLoss]
  have hhalf :=
    projectedLoss_completion_card_eq_half_target
      C exponent hvLoss
  omega

theorem projectedLoss_activeStar_target_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent) :
    2 ^ exponent v ≤
      (activeStarCandidateBlock C v).card := by
  have hcard :=
    projectedLoss_activeStar_card_times_two
      C exponent hvLoss
  have hnonneg : 2 ≤ n - exponent v + 2 := by omega
  omega

theorem projectedLoss_activeStar_slack_ge_half_target
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n) :
    (retainedCompletionWords C v).card ≤
      (activeStarCandidateBlock C v).card -
        2 ^ exponent v := by
  have hactiveCard :=
    projectedLoss_retainedActive_card C exponent hvLoss
  have hstar :=
    activeStarCandidateBlock_card C v
  have hhalf :=
    projectedLoss_completion_card_eq_half_target
      C exponent hvLoss
  have htwoActive :
      2 ≤ (retainedActive C v).card := by
    rw [hactiveCard]
    omega
  omega

theorem projectedLoss_activeStar_slack_add_one_shared_requirement
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {T : Finset V}
    (hdef : BlockDeficient demand blocks T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient demand blocks U)
    {v : V}
    (hv : v ∈ T)
    {q : ℕ}
    (hlocal : demand v + q ≤ (blocks v).card) :
    q + 1 ≤ (sharedBlockWords blocks T v).card := by
  have hbound :=
    minimal_deficient_shared_card_ge_slack_add_one
      demand blocks hdef hmin hv
      (by omega)
  omega

#print axioms projectedLoss_retainedActive_card
#print axioms projectedLoss_completion_card_eq_half_target
#print axioms projectedLoss_activeStar_card_times_two
#print axioms projectedLoss_activeStar_slack_ge_half_target

end OrderedEdgeColoring
end JSP000404Research
