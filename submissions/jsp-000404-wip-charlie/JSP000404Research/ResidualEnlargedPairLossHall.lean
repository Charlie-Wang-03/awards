import JSP000404Research.ResidualEnlargedCandidateBlock
import JSP000404Research.ResidualLossAllActivePairOverlap
import Mathlib.Tactic

/-!
# Pairwise weighted Hall expansion whenever one centre is projected loss

Let B_v be the enlarged all-retained-active candidate block. At each
projected-loss centre, B_v has at least one full completion cube Q_v
of slack beyond the dyadic target. Two loss blocks intersect in at most
|Q_v|+|Q_w|; a loss and nonloss block intersect in at most |Q_loss|.
Thus for distinct vertices with at least one projected loss, the
two candidate blocks meet their *combined* target mass.

Consequently an enlarged-candidate minimal deficient two-vertex core
cannot contain a projected-loss centre. This is an unconditional
two-vertex exclusion under the one-layer residual hypotheses.
It does not prove Hall expansion for three or more vertices.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem enlargedCandidate_pair_capacity_of_one_loss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvw : v ≠ w)
    (hSomeLoss :
      v ∈ projectedLossVertices C exponent ∨
      w ∈ projectedLossVertices C exponent) :
    2 ^ exponent v + 2 ^ exponent w ≤
      (enlargedProjectedCandidateBlock C exponent v ∪
        enlargedProjectedCandidateBlock C exponent w).card := by
  classical
  let B := enlargedProjectedCandidateBlock C exponent
  have hcardUnion :=
    Finset.card_union_add_card_inter (B v) (B w)
  have hlocalV :=
    enlargedProjectedCandidateBlock_local_capacity
      C exponent hexpLt hexp honeLoss v
  have hlocalW :=
    enlargedProjectedCandidateBlock_local_capacity
      C exponent hexpLt hexp honeLoss w
  change 2 ^ exponent v ≤ (B v).card at hlocalV
  change 2 ^ exponent w ≤ (B w).card at hlocalW
  by_cases hvLoss : v ∈ projectedLossVertices C exponent
  · have hslackV :=
      enlargedProjectedCandidateBlock_loss_slack
        C exponent hvLoss (hexpLt v)
    change 2 ^ exponent v +
      (retainedCompletionWords C v).card ≤ (B v).card at hslackV
    by_cases hwLoss : w ∈ projectedLossVertices C exponent
    · have hslackW :=
        enlargedProjectedCandidateBlock_loss_slack
          C exponent hwLoss (hexpLt w)
      change 2 ^ exponent w +
        (retainedCompletionWords C w).card ≤ (B w).card at hslackW
      have hinter :
          (B v ∩ B w).card ≤
            (retainedCompletionWords C v).card +
            (retainedCompletionWords C w).card := by
        dsimp [B]
        rw [enlargedProjectedCandidateBlock_loss C exponent hvLoss,
          enlargedProjectedCandidateBlock_loss C exponent hwLoss]
        exact loss_allActive_pair_intersection_card_le_sum_cubes
          C exponent hexp honeLoss hvLoss hwLoss hvw
      omega
    · have hinter :
          (B v ∩ B w).card ≤
            (retainedCompletionWords C v).card := by
        dsimp [B]
        rw [enlargedProjectedCandidateBlock_loss C exponent hvLoss,
          enlargedProjectedCandidateBlock_nonloss C exponent hwLoss]
        exact allActiveLossCandidateBlock_inter_blocker_card_le_cube
          C exponent hexp honeLoss hvLoss hvw
      omega
  · have hwLoss : w ∈ projectedLossVertices C exponent :=
      hSomeLoss.resolve_left hvLoss
    have hslackW :=
      enlargedProjectedCandidateBlock_loss_slack
        C exponent hwLoss (hexpLt w)
    change 2 ^ exponent w +
      (retainedCompletionWords C w).card ≤ (B w).card at hslackW
    have hinter :
        (B v ∩ B w).card ≤
          (retainedCompletionWords C w).card := by
      dsimp [B]
      rw [enlargedProjectedCandidateBlock_nonloss C exponent hvLoss,
        enlargedProjectedCandidateBlock_loss C exponent hwLoss,
        Finset.inter_comm]
      exact allActiveLossCandidateBlock_inter_blocker_card_le_cube
        C exponent hexp honeLoss hwLoss hvw.symm
    omega

#print axioms enlargedCandidate_pair_capacity_of_one_loss

end OrderedEdgeColoring
end JSP000404Research
