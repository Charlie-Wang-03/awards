import JSP000404Research.ResidualLossPairExpansion
import JSP000404Research.ResidualEnlargedCandidateBlock
import JSP000404Research.ResidualLossAllActiveIntersection
import JSP000404Research.MinimalBlockDeficiency
import Mathlib.Tactic

/-!
# Every two-vertex set containing a loss vertex expands

Let v be projected-loss with exponent(v)<n, and let w!=v be arbitrary.

If w is loss, two-loss expansion is already available.

If w is non-loss, its enlarged block is just Q_w.  The loss block has at least
3|Q_v| words, while its intersection with Q_w has at most |Q_v| words.
Moreover the non-loss target satisfies 2^k(w) <= |Q_w|.

Hence

  2^k(v) + 2^k(w)
    <= card(B_enlarged(v) union B_enlarged(w)).

Therefore no two-vertex weighted Hall obstruction can contain a projected-loss
vertex.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedLoss_with_nonloss_enlarged_pair_expands
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwNonloss : w ∉ projectedLossVertices C exponent)
    (hvLt : exponent v < n)
    (hvw : v ≠ w) :
    2 ^ exponent v + 2 ^ exponent w ≤
      (enlargedProjectedCandidateBlock C exponent v ∪
        enlargedProjectedCandidateBlock C exponent w).card := by
  classical
  rw [enlargedProjectedCandidateBlock_loss
        C exponent hvLoss,
      enlargedProjectedCandidateBlock_nonloss
        C exponent hwNonloss]
  have hv3 :=
    projectedLoss_allActiveBlock_three_cube_le
      C exponent hvLoss hvLt
  have hinter :=
    allActiveLossCandidateBlock_inter_blocker_card_le_cube
      C exponent hexp honeLoss hvLoss hvw
  have hwProj :=
    exponent_le_projectedFree_add_one
      C exponent hexp honeLoss w
  have hwNe :
      exponent w ≠ projectedFree C w + 1 := by
    intro hEq
    exact hwNonloss
      ((mem_projectedLossVertices C exponent w).2 hEq)
  have hwLe : exponent w ≤ projectedFree C w := by
    omega
  have hwTarget :=
    nonloss_completionBlock_target_le
      C exponent hwLe
  have hvTarget :=
    projectedLoss_target_eq_two_mul_completion
      C exponent hvLoss
  have hunion :
      (allActiveLossCandidateBlock C v ∪
        retainedCompletionWords C w).card =
      (allActiveLossCandidateBlock C v).card +
        (retainedCompletionWords C w).card -
      (allActiveLossCandidateBlock C v ∩
        retainedCompletionWords C w).card := by
    exact Finset.card_union
      (s := allActiveLossCandidateBlock C v)
      (t := retainedCompletionWords C w)
  rw [hunion, hvTarget]
  omega

theorem projectedLoss_with_any_enlarged_pair_expands
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w) :
    2 ^ exponent v + 2 ^ exponent w ≤
      (enlargedProjectedCandidateBlock C exponent v ∪
        enlargedProjectedCandidateBlock C exponent w).card := by
  by_cases hwLoss : w ∈ projectedLossVertices C exponent
  · exact two_projectedLoss_enlarged_blocks_expand
      C exponent hexp honeLoss
      hvLoss hwLoss (hexpLt v) (hexpLt w) hvw
  · exact projectedLoss_with_nonloss_enlarged_pair_expands
      C exponent hexp honeLoss
      hvLoss hwLoss (hexpLt v) hvw

theorem no_two_vertex_deficient_set_containing_loss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvw : v ≠ w)
    (hvLoss : v ∈ projectedLossVertices C exponent) :
    ¬ BlockDeficient
      (fun x => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      {v,w} := by
  intro hdef
  unfold BlockDeficient at hdef
  have hexpand :=
    projectedLoss_with_any_enlarged_pair_expands
      C exponent hexpLt hexp honeLoss hvLoss hvw
  have hsum :
      (∑ x ∈ ({v,w} : Finset V), 2 ^ exponent x)
        =
      2 ^ exponent v + 2 ^ exponent w := by
    simp [hvw]
  have hunion :
      (({v,w} : Finset V).biUnion
        (enlargedProjectedCandidateBlock C exponent))
        =
      enlargedProjectedCandidateBlock C exponent v ∪
        enlargedProjectedCandidateBlock C exponent w := by
    ext word
    simp
  rw [hsum,hunion] at hdef
  omega

#print axioms projectedLoss_with_any_enlarged_pair_expands
#print axioms no_two_vertex_deficient_set_containing_loss

end OrderedEdgeColoring
end JSP000404Research
