import JSP000404Research.ResidualEnlargedLossLeafRigidity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Collision-degree lower bound for a maximal loss vertex

Inside a minimal deficient enlarged-candidate core, fix a projected-loss vertex
v whose completion cube has maximum cardinality among loss vertices of the
core.

Let N(v) be the set of other core vertices whose enlarged candidate blocks
intersect B(v).

Every neighbour w contributes at most 2|Q_v| shared words:

* if w is non-loss, the intersection is at most |Q_v|;
* if w is loss, maximality gives |Q_w| <= |Q_v| and the two-loss pair bound
  gives intersection <= |Q_v|+|Q_w| <= 2|Q_v|.

Hence

  card(shared(v)) <= 2 * degree(v) * |Q_v|.

Minimal deficiency gives the opposite lower bound

  card(shared(v))
    >= (card(retainedActive(v))-1) * |Q_v| + 1.

Since |Q_v|>0, these inequalities force

  card(retainedActive(v)) <= 2 * degree(v).

The previously proved unique-neighbour rigidity is the degree-one special case.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def enlargedCollisionNeighbours
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (v : V) : Finset V := by
  classical
  exact (T.erase v).filter
    (fun w => EnlargedBlocksCross C exponent v w)

@[simp] theorem mem_enlargedCollisionNeighbours
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (v w : V) :
    w ∈ enlargedCollisionNeighbours C exponent T v ↔
      w ∈ T ∧ w ≠ v ∧
      EnlargedBlocksCross C exponent v w := by
  classical
  simp [enlargedCollisionNeighbours, and_assoc, and_left_comm,
    and_comm]

theorem sharedBlockWords_subset_collisionNeighbour_intersections
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V} {v : V} :
    sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v
      ⊆
    (enlargedCollisionNeighbours C exponent T v).biUnion
      (fun w =>
        enlargedProjectedCandidateBlock C exponent v ∩
          enlargedProjectedCandidateBlock C exponent w) := by
  classical
  intro word hshared
  have hdata :=
    sharedBlockWords_has_other_block
      (enlargedProjectedCandidateBlock C exponent)
      hshared
  obtain ⟨hvWord,w,hwT,hwv,hwWord⟩ := hdata
  apply Finset.mem_biUnion.mpr
  refine ⟨w,?_,Finset.mem_inter.mpr ⟨hvWord,hwWord⟩⟩
  apply (mem_enlargedCollisionNeighbours
    C exponent T v w).2
  exact ⟨hwT,hwv,⟨word,hvWord,hwWord⟩⟩

theorem maximalLoss_neighbor_intersection_card_le_two_cube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V} {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hmaxLoss :
      ∀ z : V,
        z ∈ T →
        z ∈ projectedLossVertices C exponent →
        (retainedCompletionWords C z).card ≤
          (retainedCompletionWords C v).card)
    (hwNeighbour :
      w ∈ enlargedCollisionNeighbours C exponent T v) :
    (enlargedProjectedCandidateBlock C exponent v ∩
      enlargedProjectedCandidateBlock C exponent w).card
      ≤
    2 * (retainedCompletionWords C v).card := by
  have hwData :=
    (mem_enlargedCollisionNeighbours
      C exponent T v w).1 hwNeighbour
  have hwv : v ≠ w := Ne.symm hwData.2.1
  by_cases hwLoss : w ∈ projectedLossVertices C exponent
  · rw [enlargedProjectedCandidateBlock_loss
        C exponent hvLoss,
      enlargedProjectedCandidateBlock_loss
        C exponent hwLoss]
    have hinter :=
      loss_allActive_pair_intersection_card_le_sum_cubes
        C exponent hexp honeLoss
        hvLoss hwLoss hwv
    have hwLe := hmaxLoss w hwData.1 hwLoss
    omega
  · rw [enlargedProjectedCandidateBlock_loss
        C exponent hvLoss,
      enlargedProjectedCandidateBlock_nonloss
        C exponent hwLoss]
    have hinter :=
      allActiveLossCandidateBlock_inter_blocker_card_le_cube
        C exponent hexp honeLoss hvLoss hwv
    omega

theorem maximalLoss_shared_card_le_degree_mul_two_cube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V} {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hmaxLoss :
      ∀ z : V,
        z ∈ T →
        z ∈ projectedLossVertices C exponent →
        (retainedCompletionWords C z).card ≤
          (retainedCompletionWords C v).card) :
    (sharedBlockWords
      (enlargedProjectedCandidateBlock C exponent)
      T v).card
      ≤
    (enlargedCollisionNeighbours C exponent T v).card *
      (2 * (retainedCompletionWords C v).card) := by
  classical
  let N := enlargedCollisionNeighbours C exponent T v
  let I : V → Finset (Fin n → Bool) :=
    fun w =>
      enlargedProjectedCandidateBlock C exponent v ∩
        enlargedProjectedCandidateBlock C exponent w
  have hsub :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ⊆
      N.biUnion I := by
    exact sharedBlockWords_subset_collisionNeighbour_intersections
      C exponent
  have hcardSub :=
    Finset.card_le_card hsub
  have hunion :
      (N.biUnion I).card ≤
        ∑ w ∈ N, (I w).card :=
    Finset.card_biUnion_le
  have hpoint :
      ∑ w ∈ N, (I w).card ≤
        ∑ _w ∈ N,
          2 * (retainedCompletionWords C v).card := by
    apply Finset.sum_le_sum
    intro w hw
    exact maximalLoss_neighbor_intersection_card_le_two_cube
      C exponent hexp honeLoss
      hvLoss hmaxLoss hw
  calc
    (sharedBlockWords
      (enlargedProjectedCandidateBlock C exponent)
      T v).card
      ≤ (N.biUnion I).card := hcardSub
    _ ≤ ∑ w ∈ N, (I w).card := hunion
    _ ≤ ∑ _w ∈ N,
          2 * (retainedCompletionWords C v).card := hpoint
    _ =
      N.card * (2 * (retainedCompletionWords C v).card) := by
        simp

theorem minimal_enlargedCandidate_maxLoss_active_card_le_two_mul_degree
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {v : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hmaxLoss :
      ∀ z : V,
        z ∈ T →
        z ∈ projectedLossVertices C exponent →
        (retainedCompletionWords C z).card ≤
          (retainedCompletionWords C v).card) :
    (retainedActive C v).card ≤
      2 * (enlargedCollisionNeighbours C exponent T v).card := by
  classical
  let a := (retainedActive C v).card
  let q := (retainedCompletionWords C v).card
  let d := (enlargedCollisionNeighbours C exponent T v).card

  have hactiveGe : 2 ≤ a := by
    dsimp [a]
    exact projectedLoss_active_card_ge_two_of_exponent_lt_n
      C exponent hvLoss (hexpLt v)

  have hqPos : 0 < q := by
    dsimp [q]
    rw [retainedCompletionWords_card]
    positivity

  have hlocal :
      2 ^ exponent v ≤
        (enlargedProjectedCandidateBlock C exponent v).card :=
    enlargedProjectedCandidateBlock_local_capacity
      C exponent hexpLt hexp honeLoss v

  have hsharedLower :=
    minimal_deficient_shared_card_ge_slack_add_one
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef hmin hvT hlocal

  have hblock :
      (enlargedProjectedCandidateBlock C exponent v).card =
        (a + 1) * q := by
    rw [enlargedProjectedCandidateBlock_loss
      C exponent hvLoss]
    exact allActiveLossCandidateBlock_card C v

  have htarget :
      2 ^ exponent v = 2 * q := by
    dsimp [q]
    exact projectedLoss_target_eq_two_mul_completion
      C exponent hvLoss

  have hsharedUpper :=
    maximalLoss_shared_card_le_degree_mul_two_cube
      C exponent hexp honeLoss hvLoss hmaxLoss
  change
    (sharedBlockWords
      (enlargedProjectedCandidateBlock C exponent)
      T v).card ≤ d * (2 * q) at hsharedUpper

  have haSplit : a = (a - 1) + 1 := by
    omega
  have hslack :
      (a + 1) * q - 2 * q = (a - 1) * q := by
    rw [haSplit]
    ring

  rw [hblock, htarget, hslack] at hsharedLower

  by_contra hdegree
  have h2dLt : 2 * d < a := by omega
  have h2dLe : 2 * d ≤ a - 1 := by omega
  have hmul :
      d * (2 * q) ≤ (a - 1) * q := by
    have hmul' := Nat.mul_le_mul_right q h2dLe
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using hmul'
  omega

#print axioms maximalLoss_shared_card_le_degree_mul_two_cube
#print axioms minimal_enlargedCandidate_maxLoss_active_card_le_two_mul_degree

end OrderedEdgeColoring
end JSP000404Research
