import JSP000404Research.ResidualLossAllActiveCandidateBlock
import JSP000404Research.ResidualProjectionLoss
import Mathlib.Tactic

/-!
# Enlarged candidate family using all active translations at loss vertices

Define one Boolean candidate block for every vertex:

* non-loss vertex v:
    B(v) = Q_v;
* projected-loss vertex v:
    B(v) = Q_v union all active one-coordinate translates of Q_v.

Under the standard one-layer projected profile and the strict exponent bound
exponent(v) < n, every block contains at least its full dyadic target mass
2^exponent(v).

At a loss vertex the block has an additional local slack of at least |Q_v|.
This is stronger than the canonical doubled block, which has exactly target
size at a loss vertex.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def enlargedProjectedCandidateBlock
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (v : V) : Finset (Fin n → Bool) := by
  classical
  exact if v ∈ projectedLossVertices C exponent then
    allActiveLossCandidateBlock C v
  else
    retainedCompletionWords C v

theorem enlargedProjectedCandidateBlock_loss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hv : v ∈ projectedLossVertices C exponent) :
    enlargedProjectedCandidateBlock C exponent v =
      allActiveLossCandidateBlock C v := by
  classical
  simp [enlargedProjectedCandidateBlock, hv]

theorem enlargedProjectedCandidateBlock_nonloss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hv : v ∉ projectedLossVertices C exponent) :
    enlargedProjectedCandidateBlock C exponent v =
      retainedCompletionWords C v := by
  classical
  simp [enlargedProjectedCandidateBlock, hv]

theorem enlargedProjectedCandidateBlock_local_capacity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ v, exponent v < n)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (v : V) :
    2 ^ exponent v ≤
      (enlargedProjectedCandidateBlock C exponent v).card := by
  classical
  by_cases hvLoss : v ∈ projectedLossVertices C exponent
  · rw [enlargedProjectedCandidateBlock_loss C exponent hvLoss]
    have hplus :=
      projectedLoss_allActiveBlock_target_plus_cube_le
        C exponent hvLoss (hexpLt v)
    exact le_trans
      (Nat.le_add_right (2 ^ exponent v)
        (retainedCompletionWords C v).card)
      hplus
  · rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvLoss]
    have hproj :=
      exponent_le_projectedFree_add_one
        C exponent hexp honeLoss v
    have hneq :
        exponent v ≠ projectedFree C v + 1 := by
      intro h
      exact hvLoss
        ((mem_projectedLossVertices C exponent v).2 h)
    have hle : exponent v ≤ projectedFree C v := by
      omega
    exact nonloss_completionBlock_target_le
      C exponent hle

theorem enlargedProjectedCandidateBlock_loss_slack
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n) :
    2 ^ exponent v +
        (retainedCompletionWords C v).card
      ≤
    (enlargedProjectedCandidateBlock C exponent v).card := by
  rw [enlargedProjectedCandidateBlock_loss C exponent hvLoss]
  exact projectedLoss_allActiveBlock_target_plus_cube_le
    C exponent hvLoss hvLt

theorem enlargedProjectedCandidateBlock_shape
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (v : V) :
    enlargedProjectedCandidateBlock C exponent v =
        retainedCompletionWords C v
    ∨
    (v ∈ projectedLossVertices C exponent ∧
      enlargedProjectedCandidateBlock C exponent v =
        allActiveLossCandidateBlock C v) := by
  classical
  by_cases hv : v ∈ projectedLossVertices C exponent
  · exact Or.inr ⟨hv,
      enlargedProjectedCandidateBlock_loss C exponent hv⟩
  · exact Or.inl
      (enlargedProjectedCandidateBlock_nonloss C exponent hv)

#print axioms enlargedProjectedCandidateBlock_local_capacity
#print axioms enlargedProjectedCandidateBlock_loss_slack

end OrderedEdgeColoring
end JSP000404Research
