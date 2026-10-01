import JSP000404Research.ResidualLossAllActivePairOverlap
import JSP000404Research.ResidualLossAllActiveCandidateBlock
import Mathlib.Tactic

/-!
# Any two projected-loss enlarged blocks satisfy weighted expansion

For projected-loss vertices v != w with exponent < n,

  card B_all(v) >= 3 card Q_v,
  card B_all(w) >= 3 card Q_w,

while

  card(B_all(v) ∩ B_all(w))
    <= card Q_v + card Q_w.

Therefore

  card(B_all(v) ∪ B_all(w))
    >= 2 card Q_v + 2 card Q_w
    = 2^exponent(v) + 2^exponent(w).

So a pair of loss vertices can never by itself be a weighted Hall-deficient
set for the enlarged candidate family.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedLoss_target_eq_two_mul_completion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent) :
    2 ^ exponent v =
      2 * (retainedCompletionWords C v).card := by
  have hlossEq :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  rw [retainedCompletionWords_card]
  unfold projectedFree at hlossEq
  rw [hlossEq, pow_succ]
  omega

theorem projectedLoss_allActiveBlock_three_cube_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n) :
    3 * (retainedCompletionWords C v).card ≤
      (allActiveLossCandidateBlock C v).card := by
  rw [allActiveLossCandidateBlock_card]
  have hactive :=
    projectedLoss_active_card_ge_two_of_exponent_lt_n
      C exponent hvLoss hvLt
  have hmul :=
    Nat.mul_le_mul_right
      (retainedCompletionWords C v).card
      (show 3 ≤ (retainedActive C v).card + 1 by omega)
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul

theorem two_projectedLoss_allActive_blocks_expand
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n)
    (hwLt : exponent w < n)
    (hvw : v ≠ w) :
    2 ^ exponent v + 2 ^ exponent w ≤
      (allActiveLossCandidateBlock C v ∪
        allActiveLossCandidateBlock C w).card := by
  classical
  have hv3 :=
    projectedLoss_allActiveBlock_three_cube_le
      C exponent hvLoss hvLt
  have hw3 :=
    projectedLoss_allActiveBlock_three_cube_le
      C exponent hwLoss hwLt
  have hinter :=
    loss_allActive_pair_intersection_card_le_sum_cubes
      C exponent hexp honeLoss hvLoss hwLoss hvw
  have hunion :
      (allActiveLossCandidateBlock C v ∪
        allActiveLossCandidateBlock C w).card =
      (allActiveLossCandidateBlock C v).card +
        (allActiveLossCandidateBlock C w).card -
      (allActiveLossCandidateBlock C v ∩
        allActiveLossCandidateBlock C w).card := by
    exact Finset.card_union
  have hvTarget :=
    projectedLoss_target_eq_two_mul_completion
      C exponent hvLoss
  have hwTarget :=
    projectedLoss_target_eq_two_mul_completion
      C exponent hwLoss
  rw [hunion, hvTarget, hwTarget]
  omega

theorem two_projectedLoss_enlarged_blocks_expand
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n)
    (hwLt : exponent w < n)
    (hvw : v ≠ w) :
    2 ^ exponent v + 2 ^ exponent w ≤
      (enlargedProjectedCandidateBlock C exponent v ∪
        enlargedProjectedCandidateBlock C exponent w).card := by
  rw [enlargedProjectedCandidateBlock_loss
        C exponent hvLoss,
      enlargedProjectedCandidateBlock_loss
        C exponent hwLoss]
  exact two_projectedLoss_allActive_blocks_expand
    C exponent hexp honeLoss
    hvLoss hwLoss hvLt hwLt hvw

#print axioms two_projectedLoss_allActive_blocks_expand
#print axioms two_projectedLoss_enlarged_blocks_expand

end OrderedEdgeColoring
end JSP000404Research
