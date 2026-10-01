import JSP000404Research.ResidualEnlargedLossLeafRigidity
import JSP000404Research.ResidualMixedOverlapForest
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
  have hdecomp :
      (a + 1) * q = 2 * q + (a - 1) * q := by
    rw [haSplit]
    ring
  rw [hblock, htarget, hdecomp,
      Nat.add_sub_cancel_left] at hsharedLower

  by_contra hdegree
  have h2dLt : 2 * d < a := by omega
  have h2dLe : 2 * d ≤ a - 1 := by omega
  have hmul :
      d * (2 * q) ≤ (a - 1) * q := by
    have hmul' := Nat.mul_le_mul_right q h2dLe
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using hmul'
  omega


theorem minimal_enlargedCandidate_maxLoss_degree_one_exponent_eq_n_sub_one
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
          (retainedCompletionWords C v).card)
    (hdegree :
      (enlargedCollisionNeighbours C exponent T v).card = 1) :
    exponent v = n - 1 := by
  have hactiveLe :=
    minimal_enlargedCandidate_maxLoss_active_card_le_two_mul_degree
      C exponent hexpLt hexp honeLoss
      hdef hmin hvT hvLoss hmaxLoss
  rw [hdegree] at hactiveLe
  have hactiveGe :=
    projectedLoss_active_card_ge_two_of_exponent_lt_n
      C exponent hvLoss (hexpLt v)
  have hactiveEq :
      (retainedActive C v).card = 2 := by
    omega
  have hloss :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  unfold projectedFree at hloss
  omega


theorem minimal_enlargedCandidate_strict_nonloss_unique_exactNeighbor_is_mixedUnpaid
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    {v w : V}
    (hvT : v ∈ T)
    (hvNonloss : v ∉ projectedLossVertices C exponent)
    (hvStrict : exponent v < projectedFree C v)
    (hwNonloss : w ∉ projectedLossVertices C exponent)
    (hwExact : ExactProjectedBudget C exponent w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    MixedUnpaidChild C exponent w v := by
  classical
  have hvLocal :
      2 ^ exponent v ≤
        (enlargedProjectedCandidateBlock C exponent v).card := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss]
    exact nonloss_completionBlock_target_le
      C exponent (Nat.le_of_lt hvStrict)
  have hsharedLower :=
    minimal_deficient_shared_card_ge_slack_add_one
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef hmin hvT hvLocal

  have hsharedNonempty :
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).Nonempty := by
    apply Finset.card_pos.mp
    have hQpos :
        0 < (retainedCompletionWords C v).card := by
      rw [retainedCompletionWords_card]
      positivity
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss] at hsharedLower
    omega

  obtain ⟨word,hwordShared⟩ := hsharedNonempty
  have hdata :=
    sharedBlockWords_has_other_block
      (enlargedProjectedCandidateBlock C exponent)
      hwordShared
  obtain ⟨hvWordBlock,z,hzT,hzv,hzWordBlock⟩ := hdata
  have hzCross : EnlargedBlocksCross C exponent v z := by
    exact ⟨word,hvWordBlock,hzWordBlock⟩
  have hzw : z = w := hunique z hzT hzv hzCross
  subst z
  have hwT : w ∈ T := hzT
  have hwv : w ≠ v := hzv

  have hvWord :
      word ∈ retainedCompletionWords C v := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss] at hvWordBlock
    exact hvWordBlock
  have hwWord :
      word ∈ retainedCompletionWords C w := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hwNonloss] at hzWordBlock
    exact hzWordBlock

  have hsharedSub :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ⊆
      retainedCompletionWords C v ∩
        retainedCompletionWords C w := by
    intro y hy
    have hyData :=
      sharedBlockWords_has_other_block
        (enlargedProjectedCandidateBlock C exponent)
        hy
    obtain ⟨hyV,z,hzT',hzv',hyZ⟩ := hyData
    have hzCross' : EnlargedBlocksCross C exponent v z := by
      exact ⟨y,hyV,hyZ⟩
    have hzw' := hunique z hzT' hzv' hzCross'
    subst z
    rw [enlargedProjectedCandidateBlock_nonloss
          C exponent hvNonloss] at hyV
    rw [enlargedProjectedCandidateBlock_nonloss
          C exponent hwNonloss] at hyZ
    exact Finset.mem_inter.mpr ⟨hyV,hyZ⟩

  have hsharedUpper :=
    Finset.card_le_card hsharedSub
  have hQcard :
      (enlargedProjectedCandidateBlock C exponent v).card =
        (retainedCompletionWords C v).card := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss]
  rw [hQcard] at hsharedLower

  have hunpaid :
      ¬ ((retainedCompletionWords C w ∩
          retainedCompletionWords C v).card
        ≤
        dyadicProfileSurplus exponent (projectedFree C) v) := by
    intro hpaid
    have hsurplus :
        dyadicProfileSurplus exponent (projectedFree C) v =
          (retainedCompletionWords C v).card -
            2 ^ exponent v := by
      unfold dyadicProfileSurplus
      rw [retainedCompletionWords_card]
    have hinterComm :
        (retainedCompletionWords C v ∩
          retainedCompletionWords C w).card
          =
        (retainedCompletionWords C w ∩
          retainedCompletionWords C v).card := by
      rw [Finset.inter_comm]
    rw [hinterComm] at hsharedUpper
    rw [hsurplus] at hpaid
    omega

  exact ⟨hwv,hwExact,hvStrict,
    word,hwWord,hvWord,hunpaid⟩

theorem minimal_enlargedCandidate_strict_nonloss_unique_exactNeighbor_exponent_lt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    {v w : V}
    (hvT : v ∈ T)
    (hvNonloss : v ∉ projectedLossVertices C exponent)
    (hvStrict : exponent v < projectedFree C v)
    (hwNonloss : w ∉ projectedLossVertices C exponent)
    (hwExact : ExactProjectedBudget C exponent w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    exponent v < exponent w := by
  exact mixedUnpaidChild_exponent_lt C exponent
    (minimal_enlargedCandidate_strict_nonloss_unique_exactNeighbor_is_mixedUnpaid
      C exponent hdef hmin hvT
      hvNonloss hvStrict hwNonloss hwExact hunique)


theorem minimal_enlargedCandidate_strict_nonloss_unique_lossNeighbor_exponent_lt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    {v w : V}
    (hvT : v ∈ T)
    (hvNonloss : v ∉ projectedLossVertices C exponent)
    (hvStrict : exponent v < projectedFree C v)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    exponent v < exponent w := by
  classical
  have hvLocal :
      2 ^ exponent v ≤
        (enlargedProjectedCandidateBlock C exponent v).card := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss]
    exact nonloss_completionBlock_target_le
      C exponent (Nat.le_of_lt hvStrict)
  have hsharedLower :=
    minimal_deficient_shared_card_ge_slack_add_one
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef hmin hvT hvLocal

  have hsharedNonempty :
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).Nonempty := by
    apply Finset.card_pos.mp
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss] at hsharedLower
    have hqPos :
        0 < (retainedCompletionWords C v).card := by
      rw [retainedCompletionWords_card]
      positivity
    omega

  obtain ⟨word,hwordShared⟩ := hsharedNonempty
  have hdata :=
    sharedBlockWords_has_other_block
      (enlargedProjectedCandidateBlock C exponent)
      hwordShared
  obtain ⟨hvWord,z,hzT,hzv,hzWord⟩ := hdata
  have hzCross : EnlargedBlocksCross C exponent v z := by
    exact ⟨word,hvWord,hzWord⟩
  have hzw : z = w := hunique z hzT hzv hzCross
  subst z
  have hwv : w ≠ v := hzv

  have hsharedSub :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ⊆
      enlargedProjectedCandidateBlock C exponent v ∩
        enlargedProjectedCandidateBlock C exponent w := by
    exact sharedBlockWords_subset_single_neighbor_intersection
      (enlargedProjectedCandidateBlock C exponent)
      hvT
      (by
        intro z hzT' hzv' hcross
        exact hunique z hzT' hzv' hcross)

  have hsharedUpper :=
    Finset.card_le_card hsharedSub
  rw [enlargedProjectedCandidateBlock_nonloss
        C exponent hvNonloss,
      enlargedProjectedCandidateBlock_loss
        C exponent hwLoss] at hsharedUpper

  have hinter :=
    allActiveLossCandidateBlock_inter_blocker_card_le_cube
      C exponent hexp honeLoss hwLoss hwv
  have hinter' :
      (retainedCompletionWords C v ∩
        allActiveLossCandidateBlock C w).card
        ≤
      (retainedCompletionWords C w).card := by
    simpa [Finset.inter_comm] using hinter
  have hsharedCube :
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card
        ≤
      (retainedCompletionWords C w).card :=
    hsharedUpper.trans hinter'

  rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss] at hsharedLower

  have hsurplusEq :
      dyadicProfileSurplus exponent (projectedFree C) v =
        (retainedCompletionWords C v).card -
          2 ^ exponent v := by
    unfold dyadicProfileSurplus
    rw [retainedCompletionWords_card]

  have hsurplusHalf :=
    half_pow_le_dyadic_surplus_of_lt hvStrict
  rw [← retainedCompletionWords_card C v] at hsurplusHalf

  have hqwGtSurplus :
      dyadicProfileSurplus exponent (projectedFree C) v <
        (retainedCompletionWords C w).card := by
    rw [hsurplusEq]
    omega

  have hfreeLe :
      projectedFree C v ≤ projectedFree C w := by
    by_contra hnot
    have hwFreeLe :
        projectedFree C w ≤ projectedFree C v - 1 := by
      omega
    have hpowLe :
        (retainedCompletionWords C w).card ≤
          2 ^ (projectedFree C v - 1) := by
      rw [retainedCompletionWords_card]
      exact Nat.pow_le_pow_right
        (by norm_num : 0 < 2) hwFreeLe
    have hhalfLe :
        2 ^ (projectedFree C v - 1) ≤
          dyadicProfileSurplus exponent (projectedFree C) v :=
      half_pow_le_dyadic_surplus_of_lt hvStrict
    omega

  have hwEq :=
    (mem_projectedLossVertices C exponent w).1 hwLoss
  unfold projectedFree at hwEq
  omega


theorem minimal_enlargedCandidate_strict_nonloss_unique_nonlossNeighbor_free_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    {v w : V}
    (hvT : v ∈ T)
    (hvNonloss : v ∉ projectedLossVertices C exponent)
    (hvStrict : exponent v < projectedFree C v)
    (hwNonloss : w ∉ projectedLossVertices C exponent)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    projectedFree C v ≤ projectedFree C w := by
  classical
  have hvLocal :
      2 ^ exponent v ≤
        (enlargedProjectedCandidateBlock C exponent v).card := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss]
    exact nonloss_completionBlock_target_le
      C exponent (Nat.le_of_lt hvStrict)
  have hsharedLower :=
    minimal_deficient_shared_card_ge_slack_add_one
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef hmin hvT hvLocal

  have hsharedNonempty :
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).Nonempty := by
    apply Finset.card_pos.mp
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss] at hsharedLower
    have hqPos :
        0 < (retainedCompletionWords C v).card := by
      rw [retainedCompletionWords_card]
      positivity
    omega

  obtain ⟨word,hwordShared⟩ := hsharedNonempty
  have hdata :=
    sharedBlockWords_has_other_block
      (enlargedProjectedCandidateBlock C exponent)
      hwordShared
  obtain ⟨hvWord,z,hzT,hzv,hzWord⟩ := hdata
  have hzCross : EnlargedBlocksCross C exponent v z := by
    exact ⟨word,hvWord,hzWord⟩
  have hzw : z = w := hunique z hzT hzv hzCross
  subst z

  have hsharedSub :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ⊆
      retainedCompletionWords C v ∩
        retainedCompletionWords C w := by
    intro y hy
    have hyData :=
      sharedBlockWords_has_other_block
        (enlargedProjectedCandidateBlock C exponent)
        hy
    obtain ⟨hyV,z,hzT',hzv',hyZ⟩ := hyData
    have hzCross' : EnlargedBlocksCross C exponent v z := by
      exact ⟨y,hyV,hyZ⟩
    have hzw' := hunique z hzT' hzv' hzCross'
    subst z
    rw [enlargedProjectedCandidateBlock_nonloss
          C exponent hvNonloss] at hyV
    rw [enlargedProjectedCandidateBlock_nonloss
          C exponent hwNonloss] at hyZ
    exact Finset.mem_inter.mpr ⟨hyV,hyZ⟩

  have hsharedUpper :=
    Finset.card_le_card hsharedSub
  rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss] at hsharedLower

  have hsurplusEq :
      dyadicProfileSurplus exponent (projectedFree C) v =
        (retainedCompletionWords C v).card -
          2 ^ exponent v := by
    unfold dyadicProfileSurplus
    rw [retainedCompletionWords_card]

  have hqwGtSurplus :
      dyadicProfileSurplus exponent (projectedFree C) v <
        (retainedCompletionWords C w).card := by
    rw [hsurplusEq]
    have hinterLe :
        (retainedCompletionWords C v ∩
          retainedCompletionWords C w).card
          ≤
        (retainedCompletionWords C w).card :=
      Finset.card_le_card Finset.inter_subset_right
    omega

  have hhalfLe :
      2 ^ (projectedFree C v - 1) ≤
        dyadicProfileSurplus exponent (projectedFree C) v :=
    half_pow_le_dyadic_surplus_of_lt hvStrict

  by_contra hnot
  have hwFreeLe :
      projectedFree C w ≤ projectedFree C v - 1 := by
    omega
  have hpowLe :
      (retainedCompletionWords C w).card ≤
        2 ^ (projectedFree C v - 1) := by
    rw [retainedCompletionWords_card]
    exact Nat.pow_le_pow_right
      (by norm_num : 0 < 2) hwFreeLe
  omega


theorem minimal_enlargedCandidate_strict_nonloss_unique_nonlossNeighbor_equalFree_blocks_eq
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    {v w : V}
    (hvT : v ∈ T)
    (hvNonloss : v ∉ projectedLossVertices C exponent)
    (hvStrict : exponent v < projectedFree C v)
    (hwNonloss : w ∉ projectedLossVertices C exponent)
    (hfreeEq : projectedFree C w = projectedFree C v)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    retainedCompletionWords C v =
      retainedCompletionWords C w := by
  classical
  have hvLocal :
      2 ^ exponent v ≤
        (enlargedProjectedCandidateBlock C exponent v).card := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss]
    exact nonloss_completionBlock_target_le
      C exponent (Nat.le_of_lt hvStrict)
  have hsharedLower :=
    minimal_deficient_shared_card_ge_slack_add_one
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef hmin hvT hvLocal

  have hsharedNonempty :
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).Nonempty := by
    apply Finset.card_pos.mp
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss] at hsharedLower
    have hqPos :
        0 < (retainedCompletionWords C v).card := by
      rw [retainedCompletionWords_card]
      positivity
    omega

  obtain ⟨base,hbaseShared⟩ := hsharedNonempty
  have hdata :=
    sharedBlockWords_has_other_block
      (enlargedProjectedCandidateBlock C exponent)
      hbaseShared
  obtain ⟨hbaseVBlock,z,hzT,hzv,hbaseZBlock⟩ := hdata
  have hzCross : EnlargedBlocksCross C exponent v z := by
    exact ⟨base,hbaseVBlock,hbaseZBlock⟩
  have hzw : z = w := hunique z hzT hzv hzCross
  subst z

  have hbaseV :
      base ∈ retainedCompletionWords C v := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss] at hbaseVBlock
    exact hbaseVBlock
  have hbaseW :
      base ∈ retainedCompletionWords C w := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hwNonloss] at hbaseZBlock
    exact hbaseZBlock

  have hsharedSub :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ⊆
      retainedCompletionWords C v ∩
        retainedCompletionWords C w := by
    intro y hy
    have hyData :=
      sharedBlockWords_has_other_block
        (enlargedProjectedCandidateBlock C exponent)
        hy
    obtain ⟨hyV,z,hzT',hzv',hyZ⟩ := hyData
    have hzCross' : EnlargedBlocksCross C exponent v z := by
      exact ⟨y,hyV,hyZ⟩
    have hzw' := hunique z hzT' hzv' hzCross'
    subst z
    rw [enlargedProjectedCandidateBlock_nonloss
          C exponent hvNonloss] at hyV
    rw [enlargedProjectedCandidateBlock_nonloss
          C exponent hwNonloss] at hyZ
    exact Finset.mem_inter.mpr ⟨hyV,hyZ⟩

  have hsharedUpper :=
    Finset.card_le_card hsharedSub
  rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss] at hsharedLower

  have hsurplusHalf :
      2 ^ (projectedFree C v - 1) ≤
        dyadicProfileSurplus exponent (projectedFree C) v :=
    half_pow_le_dyadic_surplus_of_lt hvStrict
  have hsurplusEq :
      dyadicProfileSurplus exponent (projectedFree C) v =
        (retainedCompletionWords C v).card -
          2 ^ exponent v := by
    unfold dyadicProfileSurplus
    rw [retainedCompletionWords_card]

  have hinterGtHalf :
      2 ^ (projectedFree C v - 1) <
        (retainedCompletionWords C v ∩
          retainedCompletionWords C w).card := by
    rw [hsurplusEq] at hsurplusHalf
    omega

  have hinterCard :=
    retainedCompletionWords_inter_card
      C hbaseV hbaseW
  have hcommonLe :
      (commonRetainedInactive C v w).card ≤
        projectedFree C v :=
    commonRetainedInactive_card_le_projectedFree_left
      C v w
  have hcommonEq :
      (commonRetainedInactive C v w).card =
        projectedFree C v := by
    by_contra hne
    have hcommonLePred :
        (commonRetainedInactive C v w).card ≤
          projectedFree C v - 1 := by
      omega
    have hpowLe :
        (retainedCompletionWords C v ∩
          retainedCompletionWords C w).card ≤
          2 ^ (projectedFree C v - 1) := by
      rw [hinterCard]
      exact Nat.pow_le_pow_right
        (by norm_num : 0 < 2) hcommonLePred
    omega

  have hinterEqV :
      (retainedCompletionWords C v ∩
        retainedCompletionWords C w).card =
        (retainedCompletionWords C v).card := by
    rw [hinterCard,hcommonEq,retainedCompletionWords_card]
  have hinterEqW :
      (retainedCompletionWords C v ∩
        retainedCompletionWords C w).card =
        (retainedCompletionWords C w).card := by
    rw [hinterCard,hcommonEq,retainedCompletionWords_card,hfreeEq]

  have hEqV :
      retainedCompletionWords C v ∩
        retainedCompletionWords C w =
      retainedCompletionWords C v := by
    apply Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left
    omega
  have hEqW :
      retainedCompletionWords C v ∩
        retainedCompletionWords C w =
      retainedCompletionWords C w := by
    apply Finset.eq_of_subset_of_card_le
      Finset.inter_subset_right
    omega
  exact hEqV.symm.trans hEqW


theorem minimal_enlargedCandidate_strict_nonloss_uniqueNeighbor_cube_gt_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    {v w : V}
    (hvT : v ∈ T)
    (hvNonloss : v ∉ projectedLossVertices C exponent)
    (hvStrict : exponent v < projectedFree C v)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    dyadicProfileSurplus exponent (projectedFree C) v <
      (retainedCompletionWords C w).card := by
  classical
  have hvLocal :
      2 ^ exponent v ≤
        (enlargedProjectedCandidateBlock C exponent v).card := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss]
    exact nonloss_completionBlock_target_le
      C exponent (Nat.le_of_lt hvStrict)
  have hsharedLower :=
    minimal_deficient_shared_card_ge_slack_add_one
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef hmin hvT hvLocal

  have hsharedNonempty :
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).Nonempty := by
    apply Finset.card_pos.mp
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss] at hsharedLower
    have hqPos :
        0 < (retainedCompletionWords C v).card := by
      rw [retainedCompletionWords_card]
      positivity
    omega

  obtain ⟨word,hwordShared⟩ := hsharedNonempty
  have hdata :=
    sharedBlockWords_has_other_block
      (enlargedProjectedCandidateBlock C exponent)
      hwordShared
  obtain ⟨hvWord,z,hzT,hzv,hzWord⟩ := hdata
  have hzCross : EnlargedBlocksCross C exponent v z := by
    exact ⟨word,hvWord,hzWord⟩
  have hzw : z = w := hunique z hzT hzv hzCross
  subst z
  have hwv : w ≠ v := hzv

  have hsharedSub :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ⊆
      enlargedProjectedCandidateBlock C exponent v ∩
        enlargedProjectedCandidateBlock C exponent w := by
    exact sharedBlockWords_subset_single_neighbor_intersection
      (enlargedProjectedCandidateBlock C exponent)
      hvT
      (by
        intro z hzT' hzv' hcross
        exact hunique z hzT' hzv' hcross)
  have hsharedUpper :=
    Finset.card_le_card hsharedSub

  have hpairUpper :
      (enlargedProjectedCandidateBlock C exponent v ∩
        enlargedProjectedCandidateBlock C exponent w).card
        ≤
      (retainedCompletionWords C w).card := by
    by_cases hwLoss : w ∈ projectedLossVertices C exponent
    · rw [enlargedProjectedCandidateBlock_nonloss
          C exponent hvNonloss,
        enlargedProjectedCandidateBlock_loss
          C exponent hwLoss]
      have hinter :=
        allActiveLossCandidateBlock_inter_blocker_card_le_cube
          C exponent hexp honeLoss hwLoss hwv
      simpa [Finset.inter_comm] using hinter
    · rw [enlargedProjectedCandidateBlock_nonloss
          C exponent hvNonloss,
        enlargedProjectedCandidateBlock_nonloss
          C exponent hwLoss]
      exact Finset.card_le_card Finset.inter_subset_right

  rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss] at hsharedLower
  have hsurplusEq :
      dyadicProfileSurplus exponent (projectedFree C) v =
        (retainedCompletionWords C v).card -
          2 ^ exponent v := by
    unfold dyadicProfileSurplus
    rw [retainedCompletionWords_card]
  rw [hsurplusEq]
  omega

theorem minimal_enlargedCandidate_strict_nonloss_uniqueNeighbor_free_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    {v w : V}
    (hvT : v ∈ T)
    (hvNonloss : v ∉ projectedLossVertices C exponent)
    (hvStrict : exponent v < projectedFree C v)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    projectedFree C v ≤ projectedFree C w := by
  have hgt :=
    minimal_enlargedCandidate_strict_nonloss_uniqueNeighbor_cube_gt_surplus
      C exponent hexp honeLoss
      hdef hmin hvT hvNonloss hvStrict hunique
  have hhalf :=
    half_pow_le_dyadic_surplus_of_lt hvStrict
  by_contra hnot
  have hwLe :
      projectedFree C w ≤ projectedFree C v - 1 := by
    omega
  have hpowLe :
      (retainedCompletionWords C w).card ≤
        2 ^ (projectedFree C v - 1) := by
    rw [retainedCompletionWords_card]
    exact Nat.pow_le_pow_right
      (by norm_num : 0 < 2) hwLe
  omega

theorem minimal_enlargedCandidate_strict_nonloss_leaf_progress
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    {v w : V}
    (hvT : v ∈ T)
    (hvNonloss : v ∉ projectedLossVertices C exponent)
    (hvStrict : exponent v < projectedFree C v)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    projectedFree C v < projectedFree C w
    ∨
    (
      projectedFree C v = projectedFree C w ∧
      (
        exponent v < exponent w
        ∨
        retainedCompletionWords C v =
          retainedCompletionWords C w
      )
    ) := by
  have hfreeLe :=
    minimal_enlargedCandidate_strict_nonloss_uniqueNeighbor_free_le
      C exponent hexp honeLoss
      hdef hmin hvT hvNonloss hvStrict hunique
  by_cases hfreeEq :
      projectedFree C v = projectedFree C w
  · right
    refine ⟨hfreeEq,?_⟩
    by_cases hwLoss : w ∈ projectedLossVertices C exponent
    · left
      have hwEq :=
        (mem_projectedLossVertices C exponent w).1 hwLoss
      unfold projectedFree at hwEq
      omega
    · have hwLeOne :=
        exponent_le_projectedFree_add_one
          C exponent hexp honeLoss w
      have hwNeLoss :
          exponent w ≠ projectedFree C w + 1 := by
        intro h
        exact hwLoss
          ((mem_projectedLossVertices C exponent w).2 h)
      have hwLe : exponent w ≤ projectedFree C w := by
        omega
      by_cases hwExact :
          exponent w = projectedFree C w
      · left
        omega
      · have hwStrict :
            exponent w < projectedFree C w := by
          omega
        right
        exact
          minimal_enlargedCandidate_strict_nonloss_unique_nonlossNeighbor_equalFree_blocks_eq
            C exponent hdef hmin hvT
            hvNonloss hvStrict hwLoss hfreeEq.symm hunique
  · left
    omega


def strictLeafProgressRank
    (n freeDim exponent : ℕ) : ℕ :=
  freeDim * (n + 1) + exponent

theorem strictLeafProgressRank_lt_of_free_lt
    {n freeDim freeDim' exponent exponent' : ℕ}
    (hexp : exponent ≤ n)
    (hfree : freeDim < freeDim') :
    strictLeafProgressRank n freeDim exponent <
      strictLeafProgressRank n freeDim' exponent' := by
  unfold strictLeafProgressRank
  have hstep :
      freeDim + 1 ≤ freeDim' := by
    omega
  have hmul :
      (freeDim + 1) * (n + 1) ≤
        freeDim' * (n + 1) :=
    Nat.mul_le_mul_right (n + 1) hstep
  have hgap :
      freeDim * (n + 1) + n <
        (freeDim + 1) * (n + 1) := by
    omega
  have hleft :
      freeDim * (n + 1) + exponent ≤
        freeDim * (n + 1) + n := by
    omega
  have hright :
      (freeDim + 1) * (n + 1) ≤
        freeDim' * (n + 1) + exponent' := by
    omega
  exact lt_of_le_of_lt hleft
    (lt_of_lt_of_le hgap hright)

theorem strictLeafProgressRank_lt_of_equal_free_exponent_lt
    {n freeDim exponent exponent' : ℕ}
    (hexp : exponent < exponent') :
    strictLeafProgressRank n freeDim exponent <
      strictLeafProgressRank n freeDim exponent' := by
  unfold strictLeafProgressRank
  omega

theorem minimal_enlargedCandidate_strict_nonloss_leaf_rematch_or_rank_increases
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    {v w : V}
    (hvT : v ∈ T)
    (hvNonloss : v ∉ projectedLossVertices C exponent)
    (hvStrict : exponent v < projectedFree C v)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    retainedCompletionWords C v =
        retainedCompletionWords C w
    ∨
    strictLeafProgressRank n
        (projectedFree C v) (exponent v)
      <
    strictLeafProgressRank n
        (projectedFree C w) (exponent w) := by
  rcases
    minimal_enlargedCandidate_strict_nonloss_leaf_progress
      C exponent hexp honeLoss
      hdef hmin hvT hvNonloss hvStrict hunique
    with hfree | heq
  · right
    exact strictLeafProgressRank_lt_of_free_lt
      (hexp v) hfree
  · rcases heq with ⟨hfreeEq,hexpOrBlock⟩
    rcases hexpOrBlock with hexpLt | hblocks
    · right
      rw [hfreeEq]
      exact strictLeafProgressRank_lt_of_equal_free_exponent_lt
        hexpLt
    · exact Or.inl hblocks

theorem strictLeafProgressRank_le
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (v : V) :
    strictLeafProgressRank n
        (projectedFree C v) (exponent v)
      ≤
    n * (n + 1) + n := by
  unfold strictLeafProgressRank projectedFree
  have hfree :
      n - (retainedActive C v).card ≤ n :=
    Nat.sub_le _ _
  have hmul :=
    Nat.mul_le_mul_right (n + 1) hfree
  have hvExp := hexp v
  omega


theorem minimal_enlargedCandidate_loss_uniqueNeighbor_top_or_exponent_lt
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
    {v w : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    exponent v = n - 1
    ∨
    exponent v < exponent w := by
  classical
  have hwLoss :
      w ∈ projectedLossVertices C exponent :=
    minimal_enlargedCandidate_loss_unique_neighbor_is_loss
      C exponent hexp honeLoss
      hdef hmin hvT hvLoss (hexpLt v) hunique

  have hsharedNonempty :=
    minimal_enlargedCandidate_loss_shared_nonempty
      C exponent hdef hmin hvT hvLoss (hexpLt v)
  obtain ⟨word,hwordShared⟩ := hsharedNonempty
  have hdata :=
    sharedBlockWords_has_other_block
      (enlargedProjectedCandidateBlock C exponent)
      hwordShared
  obtain ⟨hvWord,z,hzT,hzv,hzWord⟩ := hdata
  have hzCross : EnlargedBlocksCross C exponent v z := by
    exact ⟨word,hvWord,hzWord⟩
  have hzw : z = w := hunique z hzT hzv hzCross
  subst z
  have hwv : w ≠ v := hzv

  by_cases hactiveTwo :
      (retainedActive C v).card = 2
  · left
    have hloss :=
      (mem_projectedLossVertices C exponent v).1 hvLoss
    unfold projectedFree at hloss
    omega
  · right
    have hactiveGe :
        3 ≤ (retainedActive C v).card := by
      have htwo :=
        projectedLoss_active_card_ge_two_of_exponent_lt_n
          C exponent hvLoss (hexpLt v)
      omega

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

    have hsharedSub :
        sharedBlockWords
            (enlargedProjectedCandidateBlock C exponent)
            T v
          ⊆
        enlargedProjectedCandidateBlock C exponent v ∩
          enlargedProjectedCandidateBlock C exponent w :=
      sharedBlockWords_subset_single_neighbor_intersection
        (enlargedProjectedCandidateBlock C exponent)
        hvT
        (by
          intro z hzT' hzv' hcross
          exact hunique z hzT' hzv' hcross)
    have hsharedUpper :=
      Finset.card_le_card hsharedSub

    rw [enlargedProjectedCandidateBlock_loss
          C exponent hvLoss,
        enlargedProjectedCandidateBlock_loss
          C exponent hwLoss] at hsharedUpper
    have hinter :=
      loss_allActive_pair_intersection_card_le_sum_cubes
        C exponent hexp honeLoss
        hvLoss hwLoss (Ne.symm hwv)
    have hupper :
        (sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v).card
          ≤
        (retainedCompletionWords C v).card +
          (retainedCompletionWords C w).card :=
      hsharedUpper.trans hinter

    rw [enlargedProjectedCandidateBlock_loss
          C exponent hvLoss,
        allActiveLossCandidateBlock_card,
        projectedLoss_target_eq_two_mul_completion
          C exponent hvLoss] at hsharedLower

    have hqPos :
        0 < (retainedCompletionWords C v).card := by
      rw [retainedCompletionWords_card]
      positivity

    have hqwGt :
        (retainedCompletionWords C v).card <
          (retainedCompletionWords C w).card := by
      by_contra hnot
      have hqwLe :
          (retainedCompletionWords C w).card ≤
            (retainedCompletionWords C v).card := by
        omega
      omega

    have hfreeLt :
        projectedFree C v < projectedFree C w := by
      by_contra hnot
      have hwFreeLe :
          projectedFree C w ≤ projectedFree C v := by
        omega
      have hpowLe :
          (retainedCompletionWords C w).card ≤
            (retainedCompletionWords C v).card := by
        rw [retainedCompletionWords_card,
            retainedCompletionWords_card]
        exact Nat.pow_le_pow_right
          (by norm_num : 0 < 2) hwFreeLe
      omega

    have hvEq :=
      (mem_projectedLossVertices C exponent v).1 hvLoss
    have hwEq :=
      (mem_projectedLossVertices C exponent w).1 hwLoss
    unfold projectedFree at hvEq hwEq
    omega


noncomputable def lossLeafParentSliceWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (v w : V)
    (hvw : v < w)
    (hret : (C.color v w).val < n) :
    Finset (Fin n → Bool) :=
  sharedBlockWords
      (enlargedProjectedCandidateBlock C exponent)
      T v
    ∩
  translatedCompletionWords C w
    (retainedColor C v w hret)

theorem minimal_enlargedCandidate_loss_leaf_shared_le_cube_add_parentSlice_of_lt
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
    {v w : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v < w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    let hret :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hvLoss hvw
    (sharedBlockWords
      (enlargedProjectedCandidateBlock C exponent)
      T v).card
      ≤
    (retainedCompletionWords C v).card +
      (lossLeafParentSliceWords
        C exponent T v w hvw hret).card := by
  classical
  dsimp
  let hret :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss hvLoss hvw
  let e := retainedColor C v w hret

  have hwLoss :
      w ∈ projectedLossVertices C exponent :=
    minimal_enlargedCandidate_loss_unique_neighbor_is_loss
      C exponent hexp honeLoss
      hdef hmin hvT hvLoss (hexpLt v) hunique

  have hsharedSubPair :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ⊆
      enlargedProjectedCandidateBlock C exponent v ∩
        enlargedProjectedCandidateBlock C exponent w :=
    sharedBlockWords_subset_single_neighbor_intersection
      (enlargedProjectedCandidateBlock C exponent)
      hvT
      (by
        intro z hzT hzv hcross
        exact hunique z hzT hzv hcross)

  have hpairSub :=
    loss_allActive_pair_intersection_subset_edge_slices_of_lt
      C exponent hexp honeLoss
      hvLoss hwLoss hvw hret

  have hsharedSub :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ⊆
      translatedCompletionWords C v e ∪
        lossLeafParentSliceWords
          C exponent T v w hvw hret := by
    intro word hword
    have hpair := hsharedSubPair hword
    rw [enlargedProjectedCandidateBlock_loss
          C exponent hvLoss,
        enlargedProjectedCandidateBlock_loss
          C exponent hwLoss] at hpair
    have hslices := hpairSub hpair
    rcases Finset.mem_union.mp hslices with hvSlice | hwSlice
    · exact Finset.mem_union_left _ hvSlice
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hword,hwSlice⟩

  calc
    (sharedBlockWords
      (enlargedProjectedCandidateBlock C exponent)
      T v).card
      ≤
    (translatedCompletionWords C v e ∪
      lossLeafParentSliceWords
        C exponent T v w hvw hret).card :=
      Finset.card_le_card hsharedSub
    _ ≤
      (translatedCompletionWords C v e).card +
        (lossLeafParentSliceWords
          C exponent T v w hvw hret).card :=
      Finset.card_union_le _ _
    _ =
      (retainedCompletionWords C v).card +
        (lossLeafParentSliceWords
          C exponent T v w hvw hret).card := by
      rw [translatedCompletionWords_card]

theorem minimal_enlargedCandidate_loss_leaf_excess_le_parentSlice_of_lt
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
    {v w : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v < w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    let hret :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hvLoss hvw
    (sharedBlockWords
      (enlargedProjectedCandidateBlock C exponent)
      T v).card -
      (
        (enlargedProjectedCandidateBlock C exponent v).card -
          2 ^ exponent v
      )
      ≤
    (lossLeafParentSliceWords
      C exponent T v w hvw hret).card := by
  dsimp
  let hret :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss hvLoss hvw
  have hshared :=
    minimal_enlargedCandidate_loss_leaf_shared_le_cube_add_parentSlice_of_lt
      C exponent hexpLt hexp honeLoss
      hdef hmin hvT hvLoss hvw hunique
  have hslack :
      (retainedCompletionWords C v).card ≤
        (enlargedProjectedCandidateBlock C exponent v).card -
          2 ^ exponent v := by
    rw [enlargedProjectedCandidateBlock_loss
          C exponent hvLoss,
        allActiveLossCandidateBlock_card,
        projectedLoss_target_eq_two_mul_completion
          C exponent hvLoss]
    have hactive :=
      projectedLoss_active_card_ge_two_of_exponent_lt_n
        C exponent hvLoss (hexpLt v)
    have hqPos :
        0 < (retainedCompletionWords C v).card := by
      rw [retainedCompletionWords_card]
      positivity
    have hdecomp :
        ((retainedActive C v).card + 1) *
            (retainedCompletionWords C v).card
          =
        2 * (retainedCompletionWords C v).card +
          ((retainedActive C v).card - 1) *
            (retainedCompletionWords C v).card := by
      have ha :
          (retainedActive C v).card =
            ((retainedActive C v).card - 1) + 1 := by
        omega
      rw [ha]
      ring
    rw [hdecomp, Nat.add_sub_cancel_left]
    have hcoef :
        1 ≤ (retainedActive C v).card - 1 := by
      omega
    have hmul :=
      Nat.mul_le_mul_right
        (retainedCompletionWords C v).card hcoef
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hmul
  omega


noncomputable def lossLeafParentSliceWordsOfLeft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (v w : V)
    (hwv : w < v)
    (hret : (C.color w v).val < n) :
    Finset (Fin n → Bool) :=
  sharedBlockWords
      (enlargedProjectedCandidateBlock C exponent)
      T v
    ∩
  translatedCompletionWords C w
    (retainedColor C w v hret)

theorem minimal_enlargedCandidate_loss_leaf_shared_le_cube_add_parentSlice_of_gt
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
    {v w : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwv : w < v)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    let hret :=
      projectedLoss_edge_left_retained
        C exponent hexp honeLoss hvLoss hwv
    (sharedBlockWords
      (enlargedProjectedCandidateBlock C exponent)
      T v).card
      ≤
    (retainedCompletionWords C v).card +
      (lossLeafParentSliceWordsOfLeft
        C exponent T v w hwv hret).card := by
  classical
  dsimp
  let hret :=
    projectedLoss_edge_left_retained
      C exponent hexp honeLoss hvLoss hwv
  let e := retainedColor C w v hret

  have hwLoss :
      w ∈ projectedLossVertices C exponent :=
    minimal_enlargedCandidate_loss_unique_neighbor_is_loss
      C exponent hexp honeLoss
      hdef hmin hvT hvLoss (hexpLt v) hunique

  have hsharedSubPair :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ⊆
      enlargedProjectedCandidateBlock C exponent v ∩
        enlargedProjectedCandidateBlock C exponent w :=
    sharedBlockWords_subset_single_neighbor_intersection
      (enlargedProjectedCandidateBlock C exponent)
      hvT
      (by
        intro z hzT hzv hcross
        exact hunique z hzT hzv hcross)

  have hpairSubRaw :=
    loss_allActive_pair_intersection_subset_edge_slices_of_lt
      C exponent hexp honeLoss
      hwLoss hvLoss hwv hret

  have hsharedSub :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ⊆
      translatedCompletionWords C v e ∪
        lossLeafParentSliceWordsOfLeft
          C exponent T v w hwv hret := by
    intro word hword
    have hpair := hsharedSubPair hword
    rw [enlargedProjectedCandidateBlock_loss
          C exponent hvLoss,
        enlargedProjectedCandidateBlock_loss
          C exponent hwLoss] at hpair
    have hpair' :
        word ∈
          allActiveLossCandidateBlock C w ∩
            allActiveLossCandidateBlock C v := by
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hpair).2,
         (Finset.mem_inter.mp hpair).1⟩
    have hslices := hpairSubRaw hpair'
    rcases Finset.mem_union.mp hslices with hwSlice | hvSlice
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hword,hwSlice⟩
    · exact Finset.mem_union_left _ hvSlice

  calc
    (sharedBlockWords
      (enlargedProjectedCandidateBlock C exponent)
      T v).card
      ≤
    (translatedCompletionWords C v e ∪
      lossLeafParentSliceWordsOfLeft
        C exponent T v w hwv hret).card :=
      Finset.card_le_card hsharedSub
    _ ≤
      (translatedCompletionWords C v e).card +
        (lossLeafParentSliceWordsOfLeft
          C exponent T v w hwv hret).card :=
      Finset.card_union_le _ _
    _ =
      (retainedCompletionWords C v).card +
        (lossLeafParentSliceWordsOfLeft
          C exponent T v w hwv hret).card := by
      rw [translatedCompletionWords_card]

theorem minimal_enlargedCandidate_loss_leaf_excess_le_parentSlice_of_gt
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
    {v w : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwv : w < v)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    let hret :=
      projectedLoss_edge_left_retained
        C exponent hexp honeLoss hvLoss hwv
    (sharedBlockWords
      (enlargedProjectedCandidateBlock C exponent)
      T v).card -
      (
        (enlargedProjectedCandidateBlock C exponent v).card -
          2 ^ exponent v
      )
      ≤
    (lossLeafParentSliceWordsOfLeft
      C exponent T v w hwv hret).card := by
  dsimp
  let hret :=
    projectedLoss_edge_left_retained
      C exponent hexp honeLoss hvLoss hwv
  have hshared :=
    minimal_enlargedCandidate_loss_leaf_shared_le_cube_add_parentSlice_of_gt
      C exponent hexpLt hexp honeLoss
      hdef hmin hvT hvLoss hwv hunique
  have hslack :
      (retainedCompletionWords C v).card ≤
        (enlargedProjectedCandidateBlock C exponent v).card -
          2 ^ exponent v := by
    rw [enlargedProjectedCandidateBlock_loss
          C exponent hvLoss,
        allActiveLossCandidateBlock_card,
        projectedLoss_target_eq_two_mul_completion
          C exponent hvLoss]
    have hactive :=
      projectedLoss_active_card_ge_two_of_exponent_lt_n
        C exponent hvLoss (hexpLt v)
    have hdecomp :
        ((retainedActive C v).card + 1) *
            (retainedCompletionWords C v).card
          =
        2 * (retainedCompletionWords C v).card +
          ((retainedActive C v).card - 1) *
            (retainedCompletionWords C v).card := by
      have ha :
          (retainedActive C v).card =
            ((retainedActive C v).card - 1) + 1 := by
        omega
      rw [ha]
      ring
    rw [hdecomp, Nat.add_sub_cancel_left]
    have hcoef :
        1 ≤ (retainedActive C v).card - 1 := by
      omega
    have hmul :=
      Nat.mul_le_mul_right
        (retainedCompletionWords C v).card hcoef
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hmul
  omega


theorem uniqueNeighbourLeaves_enlargedBlocks_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T leaves : Finset V}
    {parent : V}
    (hleavesT : leaves ⊆ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ v ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ v →
          EnlargedBlocksCross C exponent v z →
          z = parent) :
    ((leaves : Finset V) : Set V).PairwiseDisjoint
      (enlargedProjectedCandidateBlock C exponent) := by
  intro u hu v hv huv
  classical
  rw [Finset.disjoint_left]
  intro word huWord hvWord
  have huT : u ∈ T := hleavesT hu
  have hvT : v ∈ T := hleavesT hv
  have hcross :
      EnlargedBlocksCross C exponent u v := by
    exact ⟨word,huWord,hvWord⟩
  have hvParent :
      v = parent :=
    hunique u hu v hvT huv hcross
  subst v
  exact hparentNotLeaf hv

theorem uniqueNeighbourLeafCharges_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T leaves : Finset V}
    {parent : V}
    (charge : V → Finset (Fin n → Bool))
    (hleavesT : leaves ⊆ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ v ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ v →
          EnlargedBlocksCross C exponent v z →
          z = parent)
    (hcharge :
      ∀ v ∈ leaves,
        charge v ⊆
          enlargedProjectedCandidateBlock C exponent v) :
    ((leaves : Finset V) : Set V).PairwiseDisjoint charge := by
  have hblocks :=
    uniqueNeighbourLeaves_enlargedBlocks_pairwiseDisjoint
      C exponent hleavesT hparentNotLeaf hunique
  intro u hu v hv huv
  exact Disjoint.mono
    (hcharge u hu)
    (hcharge v hv)
    (hblocks hu hv huv)

theorem uniqueNeighbourLeafCharges_sum_le_parent_allActiveTranslated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T leaves : Finset V}
    {parent : V}
    (charge : V → Finset (Fin n → Bool))
    (hleavesT : leaves ⊆ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ v ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ v →
          EnlargedBlocksCross C exponent v z →
          z = parent)
    (hchargeChild :
      ∀ v ∈ leaves,
        charge v ⊆
          enlargedProjectedCandidateBlock C exponent v)
    (hchargeParent :
      ∀ v ∈ leaves,
        charge v ⊆ allActiveTranslatedWords C parent) :
    (∑ v ∈ leaves, (charge v).card) ≤
      (allActiveTranslatedWords C parent).card := by
  classical
  have hpairwise :=
    uniqueNeighbourLeafCharges_pairwiseDisjoint
      C exponent charge
      hleavesT hparentNotLeaf hunique hchargeChild
  have hcardUnion :
      (leaves.biUnion charge).card =
        ∑ v ∈ leaves, (charge v).card := by
    rw [Finset.card_biUnion hpairwise]
  have hsub :
      leaves.biUnion charge ⊆
        allActiveTranslatedWords C parent := by
    intro word hword
    obtain ⟨v,hvLeaves,hvWord⟩ :=
      Finset.mem_biUnion.mp hword
    exact hchargeParent v hvLeaves hvWord
  have hle :=
    Finset.card_le_card hsub
  rw [hcardUnion] at hle
  exact hle

theorem uniqueNeighbourLeafCharges_sum_le_parent_active_mul_cube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T leaves : Finset V}
    {parent : V}
    (charge : V → Finset (Fin n → Bool))
    (hleavesT : leaves ⊆ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ v ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ v →
          EnlargedBlocksCross C exponent v z →
          z = parent)
    (hchargeChild :
      ∀ v ∈ leaves,
        charge v ⊆
          enlargedProjectedCandidateBlock C exponent v)
    (hchargeParent :
      ∀ v ∈ leaves,
        charge v ⊆ allActiveTranslatedWords C parent) :
    (∑ v ∈ leaves, (charge v).card) ≤
      (retainedActive C parent).card *
        (retainedCompletionWords C parent).card := by
  have hsum :=
    uniqueNeighbourLeafCharges_sum_le_parent_allActiveTranslated
      C exponent charge
      hleavesT hparentNotLeaf hunique
      hchargeChild hchargeParent
  rw [allActiveTranslatedWords_card] at hsum
  exact hsum


theorem uniqueNeighbourLeafExcess_after_lossParentSlack_le_cube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T leaves : Finset V}
    {parent : V}
    (charge excess : V → Finset (Fin n → Bool))
    (hparentLoss :
      parent ∈ projectedLossVertices C exponent)
    (hleavesT : leaves ⊆ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ v ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ v →
          EnlargedBlocksCross C exponent v z →
          z = parent)
    (hchargeChild :
      ∀ v ∈ leaves,
        charge v ⊆
          enlargedProjectedCandidateBlock C exponent v)
    (hchargeParent :
      ∀ v ∈ leaves,
        charge v ⊆ allActiveTranslatedWords C parent)
    (hexcessCharge :
      ∀ v ∈ leaves,
        (excess v).card ≤ (charge v).card) :
    (∑ v ∈ leaves, (excess v).card) -
        (
          (enlargedProjectedCandidateBlock C exponent parent).card -
            2 ^ exponent parent
        )
      ≤
    (retainedCompletionWords C parent).card := by
  classical
  have hsumCharge :=
    uniqueNeighbourLeafCharges_sum_le_parent_active_mul_cube
      C exponent charge
      hleavesT hparentNotLeaf hunique
      hchargeChild hchargeParent
  have hsumExcess :
      (∑ v ∈ leaves, (excess v).card) ≤
        ∑ v ∈ leaves, (charge v).card := by
    apply Finset.sum_le_sum
    intro v hv
    exact hexcessCharge v hv
  have hsum :
      (∑ v ∈ leaves, (excess v).card) ≤
        (retainedActive C parent).card *
          (retainedCompletionWords C parent).card :=
    hsumExcess.trans hsumCharge

  have hparentSlack :
      (enlargedProjectedCandidateBlock C exponent parent).card -
          2 ^ exponent parent
        =
      ((retainedActive C parent).card - 1) *
        (retainedCompletionWords C parent).card := by
    rw [enlargedProjectedCandidateBlock_loss
          C exponent hparentLoss,
        allActiveLossCandidateBlock_card,
        projectedLoss_target_eq_two_mul_completion
          C exponent hparentLoss]
    have hactivePos :
        1 ≤ (retainedActive C parent).card := by
      have hloss :=
        (mem_projectedLossVertices C exponent parent).1 hparentLoss
      unfold projectedFree at hloss
      have hcardLe :
          (retainedActive C parent).card ≤ n := by
        simpa using Finset.card_le_univ
          (retainedActive C parent)
      omega
    have ha :
        (retainedActive C parent).card =
          ((retainedActive C parent).card - 1) + 1 := by
      omega
    have hblockDecomp :
        ((retainedActive C parent).card + 1) *
            (retainedCompletionWords C parent).card
          =
        2 * (retainedCompletionWords C parent).card +
          ((retainedActive C parent).card - 1) *
            (retainedCompletionWords C parent).card := by
      rw [ha]
      ring
    rw [hblockDecomp, Nat.add_sub_cancel_left]

  rw [hparentSlack]
  have hdecomp :
      (retainedActive C parent).card *
          (retainedCompletionWords C parent).card
        =
      ((retainedActive C parent).card - 1) *
          (retainedCompletionWords C parent).card +
        (retainedCompletionWords C parent).card := by
    have hactivePos :
        1 ≤ (retainedActive C parent).card := by
      have hloss :=
        (mem_projectedLossVertices C exponent parent).1 hparentLoss
      unfold projectedFree at hloss
      have hcardLe :
          (retainedActive C parent).card ≤ n := by
        simpa using Finset.card_le_univ
          (retainedActive C parent)
      omega
    have ha :
        (retainedActive C parent).card =
          ((retainedActive C parent).card - 1) + 1 := by
      omega
    rw [ha]
    ring
  rw [hdecomp] at hsum
  omega


theorem minimal_enlargedCandidate_loss_leaf_deficiency_le_parentSlice_of_lt
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
    {v w : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v < w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    let hret :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hvLoss hvw
    blockDeficiencyAmount
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T
      ≤
    (lossLeafParentSliceWords
      C exponent T v w hvw hret).card := by
  dsimp
  have hlocal :=
    enlargedProjectedCandidateBlock_local_capacity
      C exponent hexpLt hexp honeLoss v
  have hglobal :=
    minimal_deficient_amount_le_shared_excess
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef hmin hvT hlocal
  have hleaf :=
    minimal_enlargedCandidate_loss_leaf_excess_le_parentSlice_of_lt
      C exponent hexpLt hexp honeLoss
      hdef hmin hvT hvLoss hvw hunique
  omega

theorem minimal_enlargedCandidate_loss_leaf_deficiency_le_parentSlice_of_gt
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
    {v w : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwv : w < v)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    let hret :=
      projectedLoss_edge_left_retained
        C exponent hexp honeLoss hvLoss hwv
    blockDeficiencyAmount
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T
      ≤
    (lossLeafParentSliceWordsOfLeft
      C exponent T v w hwv hret).card := by
  dsimp
  have hlocal :=
    enlargedProjectedCandidateBlock_local_capacity
      C exponent hexpLt hexp honeLoss v
  have hglobal :=
    minimal_deficient_amount_le_shared_excess
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef hmin hvT hlocal
  have hleaf :=
    minimal_enlargedCandidate_loss_leaf_excess_le_parentSlice_of_gt
      C exponent hexpLt hexp honeLoss
      hdef hmin hvT hvLoss hwv hunique
  omega


theorem minimal_enlargedCandidate_loss_leaf_transfer_le_parentSlice_of_lt
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
    {v w : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v < w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    let hret :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hvLoss hvw
    deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v
      ≤
    (lossLeafParentSliceWords
      C exponent T v w hvw hret).card := by
  dsimp
  have hlocal :=
    enlargedProjectedCandidateBlock_local_capacity
      C exponent hexpLt hexp honeLoss v
  rw [deletedVertexTransfer_eq_shared_minus_slack
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      T v hlocal]
  exact
    minimal_enlargedCandidate_loss_leaf_excess_le_parentSlice_of_lt
      C exponent hexpLt hexp honeLoss
      hdef hmin hvT hvLoss hvw hunique

theorem minimal_enlargedCandidate_loss_leaf_transfer_le_parentSlice_of_gt
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
    {v w : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwv : w < v)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    let hret :=
      projectedLoss_edge_left_retained
        C exponent hexp honeLoss hvLoss hwv
    deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v
      ≤
    (lossLeafParentSliceWordsOfLeft
      C exponent T v w hwv hret).card := by
  dsimp
  have hlocal :=
    enlargedProjectedCandidateBlock_local_capacity
      C exponent hexpLt hexp honeLoss v
  rw [deletedVertexTransfer_eq_shared_minus_slack
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      T v hlocal]
  exact
    minimal_enlargedCandidate_loss_leaf_excess_le_parentSlice_of_gt
      C exponent hexpLt hexp honeLoss
      hdef hmin hvT hvLoss hwv hunique

theorem minimal_enlargedCandidate_prune_loss_leaf_to_parent_of_lt
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
    {v w : V}
    (hvT : v ∈ T)
    (hwT : w ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v < w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    let transfer :=
      deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v
    let hret :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hvLoss hvw
    BlockDeficient
      (addDemandAt
        (fun x => 2 ^ exponent x) w transfer)
      (enlargedProjectedCandidateBlock C exponent)
      (T.erase v)
    ∧
    transfer ≤
      (lossLeafParentSliceWords
        C exponent T v w hvw hret).card := by
  dsimp
  constructor
  · apply minimal_deficient_delete_with_transfer_deficient
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef hmin hvT
    exact Finset.mem_erase.mpr ⟨(ne_of_lt hvw).symm,hwT⟩
  · exact
      minimal_enlargedCandidate_loss_leaf_transfer_le_parentSlice_of_lt
        C exponent hexpLt hexp honeLoss
        hdef hmin hvT hvLoss hvw hunique

theorem minimal_enlargedCandidate_prune_loss_leaf_to_parent_of_gt
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
    {v w : V}
    (hvT : v ∈ T)
    (hwT : w ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwv : w < v)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    let transfer :=
      deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v
    let hret :=
      projectedLoss_edge_left_retained
        C exponent hexp honeLoss hvLoss hwv
    BlockDeficient
      (addDemandAt
        (fun x => 2 ^ exponent x) w transfer)
      (enlargedProjectedCandidateBlock C exponent)
      (T.erase v)
    ∧
    transfer ≤
      (lossLeafParentSliceWordsOfLeft
        C exponent T v w hwv hret).card := by
  dsimp
  constructor
  · apply minimal_deficient_delete_with_transfer_deficient
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef hmin hvT
    exact Finset.mem_erase.mpr ⟨ne_of_lt hwv,hwT⟩
  · exact
      minimal_enlargedCandidate_loss_leaf_transfer_le_parentSlice_of_gt
        C exponent hexpLt hexp honeLoss
        hdef hmin hvT hvLoss hwv hunique


theorem minimal_enlargedCandidate_nonloss_leaf_transfer_le_parent_cube
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
    {v w : V}
    (hvT : v ∈ T)
    (hvNonloss : v ∉ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v
      ≤
    (retainedCompletionWords C w).card := by
  classical
  have hproj :=
    exponent_le_projectedFree_add_one
      C exponent hexp honeLoss v
  have hneq :
      exponent v ≠ projectedFree C v + 1 := by
    intro h
    exact hvNonloss
      ((mem_projectedLossVertices C exponent v).2 h)
  have hvLe : exponent v ≤ projectedFree C v := by
    omega
  have hlocal :
      2 ^ exponent v ≤
        (enlargedProjectedCandidateBlock C exponent v).card := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss]
    exact nonloss_completionBlock_target_le
      C exponent hvLe

  have htransfer :=
    deletedVertexTransfer_eq_shared_minus_slack
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      T v hlocal

  have hsharedSub :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ⊆
      enlargedProjectedCandidateBlock C exponent v ∩
        enlargedProjectedCandidateBlock C exponent w := by
    exact sharedBlockWords_subset_single_neighbor_intersection
      (enlargedProjectedCandidateBlock C exponent)
      hvT
      (by
        intro z hzT hzv hcross
        exact hunique z hzT hzv hcross)
  have hsharedUpper :=
    Finset.card_le_card hsharedSub

  have hpairUpper :
      (enlargedProjectedCandidateBlock C exponent v ∩
        enlargedProjectedCandidateBlock C exponent w).card
        ≤
      (retainedCompletionWords C w).card := by
    by_cases hwLoss : w ∈ projectedLossVertices C exponent
    · rw [enlargedProjectedCandidateBlock_nonloss
          C exponent hvNonloss,
        enlargedProjectedCandidateBlock_loss
          C exponent hwLoss]
      have hinter :=
        allActiveLossCandidateBlock_inter_blocker_card_le_cube
          C exponent hexp honeLoss hwLoss hvw.symm
      simpa [Finset.inter_comm] using hinter
    · rw [enlargedProjectedCandidateBlock_nonloss
          C exponent hvNonloss,
        enlargedProjectedCandidateBlock_nonloss
          C exponent hwLoss]
      exact Finset.card_le_card Finset.inter_subset_right

  rw [htransfer]
  omega

theorem minimal_enlargedCandidate_prune_nonloss_leaf_to_parent
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
    {v w : V}
    (hvT : v ∈ T)
    (hwT : w ∈ T)
    (hvNonloss : v ∉ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    let transfer :=
      deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v
    BlockDeficient
      (addDemandAt
        (fun x => 2 ^ exponent x) w transfer)
      (enlargedProjectedCandidateBlock C exponent)
      (T.erase v)
    ∧
    transfer ≤
      (retainedCompletionWords C w).card := by
  dsimp
  constructor
  · apply minimal_deficient_delete_with_transfer_deficient
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef hmin hvT
    exact Finset.mem_erase.mpr ⟨hvw.symm,hwT⟩
  · exact
      minimal_enlargedCandidate_nonloss_leaf_transfer_le_parent_cube
        C exponent hexpLt hexp honeLoss
        hdef hmin hvT hvNonloss hvw hunique


theorem minimal_enlargedCandidate_prune_any_leaf_to_parent
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
    {v w : V}
    (hvT : v ∈ T)
    (hwT : w ∈ T)
    (hvw : v ≠ w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    let transfer :=
      deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v
    BlockDeficient
      (addDemandAt
        (fun x => 2 ^ exponent x) w transfer)
      (enlargedProjectedCandidateBlock C exponent)
      (T.erase v)
    ∧
    transfer ≤ (retainedCompletionWords C w).card := by
  dsimp
  by_cases hvLoss :
      v ∈ projectedLossVertices C exponent
  · rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
    · obtain ⟨hdef',htransfer⟩ :=
        minimal_enlargedCandidate_prune_loss_leaf_to_parent_of_lt
          C exponent hexpLt hexp honeLoss
          hdef hmin hvT hwT hvLoss hvwlt hunique
      refine ⟨hdef',?_⟩
      let hret :=
        projectedLoss_edge_right_retained
          C exponent hexp honeLoss hvLoss hvwlt
      have hsub :
          lossLeafParentSliceWords
              C exponent T v w hvwlt hret
            ⊆
          translatedCompletionWords C w
            (retainedColor C v w hret) :=
        Finset.inter_subset_right
      have hcard :=
        Finset.card_le_card hsub
      rw [translatedCompletionWords_card] at hcard
      exact htransfer.trans hcard
    · obtain ⟨hdef',htransfer⟩ :=
        minimal_enlargedCandidate_prune_loss_leaf_to_parent_of_gt
          C exponent hexpLt hexp honeLoss
          hdef hmin hvT hwT hvLoss hwvlt hunique
      refine ⟨hdef',?_⟩
      let hret :=
        projectedLoss_edge_left_retained
          C exponent hexp honeLoss hvLoss hwvlt
      have hsub :
          lossLeafParentSliceWordsOfLeft
              C exponent T v w hwvlt hret
            ⊆
          translatedCompletionWords C w
            (retainedColor C w v hret) :=
        Finset.inter_subset_right
      have hcard :=
        Finset.card_le_card hsub
      rw [translatedCompletionWords_card] at hcard
      exact htransfer.trans hcard
  · exact
      minimal_enlargedCandidate_prune_nonloss_leaf_to_parent
        C exponent hexpLt hexp honeLoss
        hdef hmin hvT hwT hvLoss hvw hunique


theorem uniqueNeighbourLeafTransfers_sum_le_parent_block
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T leaves : Finset V}
    {parent : V}
    (transfer : V → ℕ)
    (charge : V → Finset (Fin n → Bool))
    (hleavesT : leaves ⊆ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ v ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ v →
          EnlargedBlocksCross C exponent v z →
          z = parent)
    (hchargeChild :
      ∀ v ∈ leaves,
        charge v ⊆
          enlargedProjectedCandidateBlock C exponent v)
    (hchargeParent :
      ∀ v ∈ leaves,
        charge v ⊆
          enlargedProjectedCandidateBlock C exponent parent)
    (htransfer :
      ∀ v ∈ leaves,
        transfer v ≤ (charge v).card) :
    (∑ v ∈ leaves, transfer v) ≤
      (enlargedProjectedCandidateBlock C exponent parent).card := by
  classical
  have hpairwise :=
    uniqueNeighbourLeafCharges_pairwiseDisjoint
      C exponent charge
      hleavesT hparentNotLeaf hunique hchargeChild
  have hcardUnion :
      (leaves.biUnion charge).card =
        ∑ v ∈ leaves, (charge v).card := by
    rw [Finset.card_biUnion hpairwise]
  have hsub :
      leaves.biUnion charge ⊆
        enlargedProjectedCandidateBlock C exponent parent := by
    intro word hword
    obtain ⟨v,hvLeaves,hvWord⟩ :=
      Finset.mem_biUnion.mp hword
    exact hchargeParent v hvLeaves hvWord
  have hunionLe :=
    Finset.card_le_card hsub
  rw [hcardUnion] at hunionLe
  have hsum :
      (∑ v ∈ leaves, transfer v) ≤
        ∑ v ∈ leaves, (charge v).card := by
    apply Finset.sum_le_sum
    intro v hv
    exact htransfer v hv
  exact hsum.trans hunionLe

theorem uniqueNeighbourLeafTransfers_after_nonlossParentSlack_le_cube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T leaves : Finset V}
    {parent : V}
    (transfer : V → ℕ)
    (charge : V → Finset (Fin n → Bool))
    (hparentNonloss :
      parent ∉ projectedLossVertices C exponent)
    (hleavesT : leaves ⊆ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ v ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ v →
          EnlargedBlocksCross C exponent v z →
          z = parent)
    (hchargeChild :
      ∀ v ∈ leaves,
        charge v ⊆
          enlargedProjectedCandidateBlock C exponent v)
    (hchargeParent :
      ∀ v ∈ leaves,
        charge v ⊆
          enlargedProjectedCandidateBlock C exponent parent)
    (htransfer :
      ∀ v ∈ leaves,
        transfer v ≤ (charge v).card) :
    (∑ v ∈ leaves, transfer v) -
        (
          (enlargedProjectedCandidateBlock C exponent parent).card -
            2 ^ exponent parent
        )
      ≤
    (retainedCompletionWords C parent).card := by
  have hsum :=
    uniqueNeighbourLeafTransfers_sum_le_parent_block
      C exponent transfer charge
      hleavesT hparentNotLeaf hunique
      hchargeChild hchargeParent htransfer
  have hblock :
      enlargedProjectedCandidateBlock C exponent parent =
        retainedCompletionWords C parent :=
    enlargedProjectedCandidateBlock_nonloss
      C exponent hparentNonloss
  rw [hblock] at hsum ⊢
  have hproj :=
    exponent_le_projectedFree_add_one
      C exponent hexp honeLoss parent
  have hneq :
      exponent parent ≠ projectedFree C parent + 1 := by
    intro h
    exact hparentNonloss
      ((mem_projectedLossVertices C exponent parent).2 h)
  have hle : exponent parent ≤ projectedFree C parent := by
    omega
  have htarget :
      2 ^ exponent parent ≤
        (retainedCompletionWords C parent).card :=
    nonloss_completionBlock_target_le
      C exponent hle
  omega

theorem uniqueNeighbourLeafTransfers_after_lossParentSlack_le_cube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T leaves : Finset V}
    {parent : V}
    (transfer : V → ℕ)
    (charge : V → Finset (Fin n → Bool))
    (hparentLoss :
      parent ∈ projectedLossVertices C exponent)
    (hleavesT : leaves ⊆ T)
    (hparentNotLeaf : parent ∉ leaves)
    (hunique :
      ∀ v ∈ leaves,
        ∀ z : V,
          z ∈ T →
          z ≠ v →
          EnlargedBlocksCross C exponent v z →
          z = parent)
    (hchargeChild :
      ∀ v ∈ leaves,
        charge v ⊆
          enlargedProjectedCandidateBlock C exponent v)
    (hchargeParent :
      ∀ v ∈ leaves,
        charge v ⊆ allActiveTranslatedWords C parent)
    (htransfer :
      ∀ v ∈ leaves,
        transfer v ≤ (charge v).card) :
    (∑ v ∈ leaves, transfer v) -
        (
          (enlargedProjectedCandidateBlock C exponent parent).card -
            2 ^ exponent parent
        )
      ≤
    (retainedCompletionWords C parent).card := by
  classical
  have hsumCharge :=
    uniqueNeighbourLeafCharges_sum_le_parent_active_mul_cube
      C exponent charge
      hleavesT hparentNotLeaf hunique
      hchargeChild hchargeParent
  have hsumTransfer :
      (∑ v ∈ leaves, transfer v) ≤
        ∑ v ∈ leaves, (charge v).card := by
    apply Finset.sum_le_sum
    intro v hv
    exact htransfer v hv
  have hsum :
      (∑ v ∈ leaves, transfer v) ≤
        (retainedActive C parent).card *
          (retainedCompletionWords C parent).card :=
    hsumTransfer.trans hsumCharge
  have hslack :
      (enlargedProjectedCandidateBlock C exponent parent).card -
          2 ^ exponent parent
        =
      ((retainedActive C parent).card - 1) *
        (retainedCompletionWords C parent).card := by
    rw [enlargedProjectedCandidateBlock_loss
          C exponent hparentLoss,
        allActiveLossCandidateBlock_card,
        projectedLoss_target_eq_two_mul_completion
          C exponent hparentLoss]
    have hactivePos :
        1 ≤ (retainedActive C parent).card := by
      have hloss :=
        (mem_projectedLossVertices C exponent parent).1 hparentLoss
      unfold projectedFree at hloss
      have hcardLe :
          (retainedActive C parent).card ≤ n := by
        simpa using Finset.card_le_univ
          (retainedActive C parent)
      omega
    have ha :
        (retainedActive C parent).card =
          ((retainedActive C parent).card - 1) + 1 := by
      omega
    have hdecomp :
        ((retainedActive C parent).card + 1) *
            (retainedCompletionWords C parent).card
          =
        2 * (retainedCompletionWords C parent).card +
          ((retainedActive C parent).card - 1) *
            (retainedCompletionWords C parent).card := by
      rw [ha]
      ring
    rw [hdecomp, Nat.add_sub_cancel_left]
  rw [hslack]
  have hactivePos :
      1 ≤ (retainedActive C parent).card := by
    have hloss :=
      (mem_projectedLossVertices C exponent parent).1 hparentLoss
    unfold projectedFree at hloss
    have hcardLe :
        (retainedActive C parent).card ≤ n := by
      simpa using Finset.card_le_univ
        (retainedActive C parent)
    omega
  have ha :
      (retainedActive C parent).card =
        ((retainedActive C parent).card - 1) + 1 := by
    omega
  have hmass :
      (retainedActive C parent).card *
          (retainedCompletionWords C parent).card
        =
      ((retainedActive C parent).card - 1) *
          (retainedCompletionWords C parent).card +
        (retainedCompletionWords C parent).card := by
    rw [ha]
    ring
  rw [hmass] at hsum
  omega


theorem minimal_enlargedCandidate_exact_nonloss_leaf_transfer_eq_shared
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    (hvNonloss : v ∉ projectedLossVertices C exponent)
    (hvExact : ExactProjectedBudget C exponent v) :
    deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v
      =
    (sharedBlockWords
      (enlargedProjectedCandidateBlock C exponent)
      T v).card := by
  have hblock :
      (enlargedProjectedCandidateBlock C exponent v).card =
        2 ^ exponent v := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss,
      retainedCompletionWords_card,
      hvExact]
  have hsplit :=
    block_card_eq_private_add_shared
      (enlargedProjectedCandidateBlock C exponent)
      T v
  unfold deletedVertexTransfer
  rw [hblock] at hsplit
  omega

theorem minimal_enlargedCandidate_exact_leaf_strictNeighbor_paid_or_mixedUnpaid
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    {v w : V}
    (hvT : v ∈ T)
    (hvNonloss : v ∉ projectedLossVertices C exponent)
    (hvExact : ExactProjectedBudget C exponent v)
    (hwNonloss : w ∉ projectedLossVertices C exponent)
    (hwStrict : exponent w < projectedFree C w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v
      ≤
      dyadicProfileSurplus exponent (projectedFree C) w
    ∨
    MixedUnpaidChild C exponent v w := by
  classical
  have htransferEq :=
    minimal_enlargedCandidate_exact_nonloss_leaf_transfer_eq_shared
      C exponent hdef hmin hvT hvNonloss hvExact
  by_cases hpaid :
      deletedVertexTransfer
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ≤
      dyadicProfileSurplus exponent (projectedFree C) w
  · exact Or.inl hpaid
  · right

    have hsharedNonempty :
        (sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v).Nonempty := by
      have hpos :=
        minimal_enlargedCandidate_exact_nonloss_leaf_transfer_eq_shared
          C exponent hdef hmin hvT hvNonloss hvExact
      have htransferPos :=
        minimal_deficient_deletedVertexTransfer_pos
          (fun x : V => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          hdef hmin hvT
      rw [hpos] at htransferPos
      exact Finset.card_pos.mp htransferPos

    obtain ⟨base,hbaseShared⟩ := hsharedNonempty
    have hdata :=
      sharedBlockWords_has_other_block
        (enlargedProjectedCandidateBlock C exponent)
        hbaseShared
    obtain ⟨hbaseVBlock,z,hzT,hzv,hbaseZBlock⟩ := hdata
    have hzCross :
        EnlargedBlocksCross C exponent v z :=
      ⟨base,hbaseVBlock,hbaseZBlock⟩
    have hzw : z = w :=
      hunique z hzT hzv hzCross
    subst z

    have hbaseV :
        base ∈ retainedCompletionWords C v := by
      rw [enlargedProjectedCandidateBlock_nonloss
        C exponent hvNonloss] at hbaseVBlock
      exact hbaseVBlock
    have hbaseW :
        base ∈ retainedCompletionWords C w := by
      rw [enlargedProjectedCandidateBlock_nonloss
        C exponent hwNonloss] at hbaseZBlock
      exact hbaseZBlock

    have hsharedSub :
        sharedBlockWords
            (enlargedProjectedCandidateBlock C exponent)
            T v
          ⊆
        retainedCompletionWords C v ∩
          retainedCompletionWords C w := by
      intro y hy
      have hyData :=
        sharedBlockWords_has_other_block
          (enlargedProjectedCandidateBlock C exponent)
          hy
      obtain ⟨hyV,z,hzT',hzv',hyZ⟩ := hyData
      have hzCross' :
          EnlargedBlocksCross C exponent v z :=
        ⟨y,hyV,hyZ⟩
      have hzw' := hunique z hzT' hzv' hzCross'
      subst z
      rw [enlargedProjectedCandidateBlock_nonloss
            C exponent hvNonloss] at hyV
      rw [enlargedProjectedCandidateBlock_nonloss
            C exponent hwNonloss] at hyZ
      exact Finset.mem_inter.mpr ⟨hyV,hyZ⟩

    have hsharedLe :=
      Finset.card_le_card hsharedSub
    have hunpaid :
        ¬ ((retainedCompletionWords C v ∩
            retainedCompletionWords C w).card
          ≤
          dyadicProfileSurplus exponent (projectedFree C) w) := by
      intro hoverPaid
      have htransferLe :
          deletedVertexTransfer
              (fun x => 2 ^ exponent x)
              (enlargedProjectedCandidateBlock C exponent)
              T v
            ≤
          dyadicProfileSurplus exponent (projectedFree C) w := by
        rw [htransferEq]
        exact hsharedLe.trans hoverPaid
      exact hpaid htransferLe

    exact ⟨
      (by
        intro hvwEq
        subst w
        unfold ExactProjectedBudget at hvExact
        omega),
      hvExact,
      hwStrict,
      base,hbaseV,hbaseW,hunpaid
    ⟩

theorem minimal_enlargedCandidate_exact_leaf_strictNeighbor_paid_or_descends
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    {v w : V}
    (hvT : v ∈ T)
    (hvNonloss : v ∉ projectedLossVertices C exponent)
    (hvExact : ExactProjectedBudget C exponent v)
    (hwNonloss : w ∉ projectedLossVertices C exponent)
    (hwStrict : exponent w < projectedFree C w)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    deletedVertexTransfer
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T v
      ≤
      dyadicProfileSurplus exponent (projectedFree C) w
    ∨
    exponent w < exponent v := by
  rcases
    minimal_enlargedCandidate_exact_leaf_strictNeighbor_paid_or_mixedUnpaid
      C exponent hdef hmin hvT
      hvNonloss hvExact hwNonloss hwStrict hunique
    with hpaid | hmixed
  · exact Or.inl hpaid
  · exact Or.inr
      (mixedUnpaidChild_exponent_lt C exponent hmixed)


theorem minimal_enlargedCandidate_exact_leaf_profile_outlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    {v w : V}
    (hvT : v ∈ T)
    (hvNonloss : v ∉ projectedLossVertices C exponent)
    (hvExact : ExactProjectedBudget C exponent v)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    (
      deletedVertexTransfer
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ≤
      dyadicProfileSurplus exponent (projectedFree C) w
    )
    ∨
    (
      exponent w < exponent v
    )
    ∨
    ExactProjectedBudget C exponent w
    ∨
    w ∈ projectedLossVertices C exponent := by
  rcases projectedProfile_strict_exact_or_loss
      C exponent hexp honeLoss w
    with hwStrict | hwExact | hwLoss
  · have hwNonloss :
        w ∉ projectedLossVertices C exponent := by
      intro hwLoss
      have hwEq :=
        (mem_projectedLossVertices C exponent w).1 hwLoss
      unfold projectedFree at hwEq
      omega
    rcases
      minimal_enlargedCandidate_exact_leaf_strictNeighbor_paid_or_descends
        C exponent hdef hmin hvT
        hvNonloss hvExact hwNonloss hwStrict hunique
      with hpaid | hdesc
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl hdesc)
  · exact Or.inr (Or.inr (Or.inl hwExact))
  · exact Or.inr (Or.inr (Or.inr hwLoss))


inductive EnlargedLeafOutlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (v w : V) : Prop
  | strictProgress
      (hvStrict : exponent v < projectedFree C v)
      (hprogress :
        retainedCompletionWords C v =
            retainedCompletionWords C w
        ∨
        strictLeafProgressRank n
            (projectedFree C v) (exponent v)
          <
        strictLeafProgressRank n
            (projectedFree C w) (exponent w))
  | exactOutlet
      (hvExact : ExactProjectedBudget C exponent v)
      (hout :
        deletedVertexTransfer
            (fun x => 2 ^ exponent x)
            (enlargedProjectedCandidateBlock C exponent)
            T v
          ≤
        dyadicProfileSurplus exponent (projectedFree C) w
        ∨
        exponent w < exponent v
        ∨
        ExactProjectedBudget C exponent w
        ∨
        w ∈ projectedLossVertices C exponent)
  | lossProgress
      (hvLoss : v ∈ projectedLossVertices C exponent)
      (hprogress :
        exponent v = n - 1
        ∨
        exponent v < exponent w)

theorem minimal_enlargedCandidate_any_leaf_outlet
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
    {v w : V}
    (hvT : v ∈ T)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    EnlargedLeafOutlet C exponent T v w := by
  rcases projectedProfile_strict_exact_or_loss
      C exponent hexp honeLoss v
    with hvStrict | hvExact | hvLoss
  · have hvNonloss :
        v ∉ projectedLossVertices C exponent := by
      intro hvLoss
      have hvEq :=
        (mem_projectedLossVertices C exponent v).1 hvLoss
      unfold projectedFree at hvEq
      omega
    exact EnlargedLeafOutlet.strictProgress
      hvStrict
      (minimal_enlargedCandidate_strict_nonloss_leaf_rematch_or_rank_increases
        C exponent hexp honeLoss
        hdef hmin hvT hvNonloss hvStrict hunique)
  · have hvNonloss :
        v ∉ projectedLossVertices C exponent := by
      intro hvLoss
      have hvEq :=
        (mem_projectedLossVertices C exponent v).1 hvLoss
      unfold ExactProjectedBudget projectedFree at hvExact hvEq
      omega
    exact EnlargedLeafOutlet.exactOutlet
      hvExact
      (minimal_enlargedCandidate_exact_leaf_profile_outlet
        C exponent hexp honeLoss
        hdef hmin hvT hvNonloss hvExact hunique)
  · exact EnlargedLeafOutlet.lossProgress
      hvLoss
      (minimal_enlargedCandidate_loss_uniqueNeighbor_top_or_exponent_lt
        C exponent hexpLt hexp honeLoss
        hdef hmin hvT hvLoss hunique)


theorem enlargedLoss_local_slack_eq_translated_minus_one_cube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent) :
    (enlargedProjectedCandidateBlock C exponent v).card -
        2 ^ exponent v
      =
    ((retainedActive C v).card - 1) *
      (retainedCompletionWords C v).card := by
  rw [enlargedProjectedCandidateBlock_loss
      C exponent hvLoss,
    allActiveLossCandidateBlock_card,
    projectedLoss_target_eq_two_mul_completion
      C exponent hvLoss]
  have hactivePos :
      1 ≤ (retainedActive C v).card := by
    have hloss :=
      (mem_projectedLossVertices C exponent v).1 hvLoss
    unfold projectedFree at hloss
    have hcardLe :
        (retainedActive C v).card ≤ n := by
      simpa using Finset.card_le_univ
        (retainedActive C v)
    omega
  have ha :
      (retainedActive C v).card =
        ((retainedActive C v).card - 1) + 1 := by
    omega
  rw [ha]
  ring_nf
  omega

theorem enlargedLoss_translated_region_card_eq_active_mul_cube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    (allActiveTranslatedWords C v).card
      =
    (retainedActive C v).card *
      (retainedCompletionWords C v).card := by
  exact allActiveTranslatedWords_card C v

#print axioms enlargedLoss_local_slack_eq_translated_minus_one_cube
#print axioms enlargedLoss_translated_region_card_eq_active_mul_cube

end OrderedEdgeColoring
end JSP000404Research
