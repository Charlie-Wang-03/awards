import JSP000404Research.ResidualEnlargedLossDegree
import JSP000404Research.MinimalBlockLeafTransfer
import Mathlib.Tactic

/-!
# Aggregate sibling-leaf transfer bound

For leaves with one common parent, use each leaf's shared words as its
canonical charge.  Unique-neighbour rigidity makes these charges pairwise
disjoint and contained in the parent enlarged block.

Therefore the total deleted-vertex transfer of all siblings is at most the
parent block cardinality.  After subtracting the parent's original local
slack, the residual overload is at most two retained completion cubes.  For a
non-loss parent the sharper bound is one cube.

This is the robust tree-DP invariant needed to connect the final leaf branch
to the existing small-fibre recursive machinery.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def siblingLeafCharge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (v : V) : Finset (Fin n → Bool) :=
  sharedBlockWords
    (enlargedProjectedCandidateBlock C exponent) T v

theorem siblingLeafCharge_subset_child
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (v : V) :
    siblingLeafCharge C exponent T v ⊆
      enlargedProjectedCandidateBlock C exponent v := by
  intro word hword
  exact (Finset.mem_inter.mp hword).1

theorem siblingLeafCharge_subset_parent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T leaves : Finset V}
    {parent v : V}
    (hvLeaves : v ∈ leaves)
    (hleavesT : leaves ⊆ T)
    (hparentT : parent ∈ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ u ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ u →
          EnlargedBlocksCross C exponent u z →
          z = parent) :
    siblingLeafCharge C exponent T v ⊆
      enlargedProjectedCandidateBlock C exponent parent := by
  have hvT : v ∈ T := hleavesT hvLeaves
  have hvp : v ≠ parent := by
    intro h
    subst v
    exact hparentNotLeaf hvLeaves
  have hEq :=
    sharedBlockWords_eq_unique_neighbor_intersection
      (enlargedProjectedCandidateBlock C exponent)
      hvT hparentT hvp
      (by
        intro z hzT hzv hcross
        exact hunique v hvLeaves z hzT hzv hcross)
  rw [siblingLeafCharge, hEq]
  exact Finset.inter_subset_right

theorem siblingLeafTransfer_le_charge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (T : Finset V)
    (v : V) :
    deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v
      ≤
    (siblingLeafCharge C exponent T v).card := by
  have hlocal :=
    enlargedProjectedCandidateBlock_local_capacity
      C exponent hexpLt hexp honeLoss v
  rw [deletedVertexTransfer_eq_shared_minus_slack
        (fun x : V => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v hlocal]
  simp [siblingLeafCharge]
  omega

theorem siblingLeafTransfers_sum_le_parent_block
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T leaves : Finset V}
    {parent : V}
    (hleavesT : leaves ⊆ T)
    (hparentT : parent ∈ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ v ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ v →
          EnlargedBlocksCross C exponent v z →
          z = parent) :
    (∑ v ∈ leaves,
      deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v)
      ≤
    (enlargedProjectedCandidateBlock C exponent parent).card := by
  let transfer : V → ℕ :=
    fun v =>
      deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v
  let charge : V → Finset (Fin n → Bool) :=
    fun v => siblingLeafCharge C exponent T v
  apply uniqueNeighbourLeafTransfers_sum_le_parent_block
    C exponent transfer charge
    hleavesT hparentNotLeaf hunique
  · intro v _hv
    exact siblingLeafCharge_subset_child C exponent T v
  · intro v hv
    exact siblingLeafCharge_subset_parent
      C exponent hv hleavesT hparentT hparentNotLeaf hunique
  · intro v _hv
    exact siblingLeafTransfer_le_charge
      C exponent hexpLt hexp honeLoss T v

theorem siblingLeafTransfers_after_parent_slack_le_two_cubes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T leaves : Finset V}
    {parent : V}
    (hleavesT : leaves ⊆ T)
    (hparentT : parent ∈ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ v ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ v →
          EnlargedBlocksCross C exponent v z →
          z = parent) :
    (∑ v ∈ leaves,
      deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v)
      -
      (
        (enlargedProjectedCandidateBlock C exponent parent).card -
          2 ^ exponent parent
      )
      ≤
    2 * (retainedCompletionWords C parent).card := by
  have hsum :=
    siblingLeafTransfers_sum_le_parent_block
      C exponent hexpLt hexp honeLoss
      hleavesT hparentT hparentNotLeaf hunique
  by_cases hpLoss :
      parent ∈ projectedLossVertices C exponent
  · have hblock :
        (enlargedProjectedCandidateBlock C exponent parent).card =
          ((retainedActive C parent).card + 1) *
            (retainedCompletionWords C parent).card := by
      rw [enlargedProjectedCandidateBlock_loss C exponent hpLoss]
      exact allActiveLossCandidateBlock_card C parent
    have htarget :
        2 ^ exponent parent =
          2 * (retainedCompletionWords C parent).card :=
      projectedLoss_target_eq_two_mul_completion
        C exponent hpLoss
    rw [hblock, htarget] at hsum ⊢
    omega
  · have hblock :
        enlargedProjectedCandidateBlock C exponent parent =
          retainedCompletionWords C parent :=
      enlargedProjectedCandidateBlock_nonloss
        C exponent hpLoss
    rw [hblock] at hsum ⊢
    omega

theorem siblingLeafTransfers_after_nonloss_parent_slack_le_one_cube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T leaves : Finset V}
    {parent : V}
    (hparentNonloss :
      parent ∉ projectedLossVertices C exponent)
    (hleavesT : leaves ⊆ T)
    (hparentT : parent ∈ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ v ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ v →
          EnlargedBlocksCross C exponent v z →
          z = parent) :
    (∑ v ∈ leaves,
      deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v)
      -
      (
        (enlargedProjectedCandidateBlock C exponent parent).card -
          2 ^ exponent parent
      )
      ≤
    (retainedCompletionWords C parent).card := by
  have hsum :=
    siblingLeafTransfers_sum_le_parent_block
      C exponent hexpLt hexp honeLoss
      hleavesT hparentT hparentNotLeaf hunique
  rw [enlargedProjectedCandidateBlock_nonloss
        C exponent hparentNonloss] at hsum ⊢
  omega

#print axioms siblingLeafTransfers_sum_le_parent_block
#print axioms siblingLeafTransfers_after_parent_slack_le_two_cubes
#print axioms siblingLeafTransfers_after_nonloss_parent_slack_le_one_cube

end OrderedEdgeColoring
end JSP000404Research
