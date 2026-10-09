import JSP000404Research.DirectionDataHallResidualActiveBoundary
import JSP000404Research.ResidualSliceSeparation
import JSP000404Research.MinimalBlockSharedDeficit
import Mathlib.Tactic

/-!
# G1: necessary two-sided slice-slack pressure in a minimal loss-free Hall core

In a genuine loss-free minimal Hall obstruction, every centre is
residual-active and every candidate block is its retained completion cube.
Within either fixed residual bit, these cubes are pairwise disjoint.

Consequently, Hall deficiency forces the total demand on the OPPOSITE
residual-bit side to exceed all the unused local slack on the selected side.
This is a quantitative restriction beyond simply having both bit polarities.
It does not by itself prove G1 or exclude all such cores.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The centres of T on one canonical residual-bit side. -/
noncomputable def coreResidualBitSlice
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (T : Finset V)
    (b : Bool) : Finset V :=
  T.filter (fun v => bit B v (residualCoord n) = b)

theorem coreResidualBitSlice_subset
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (T : Finset V) (b : Bool) :
    coreResidualBitSlice B T b ⊆ T := by
  intro v hv
  exact (Finset.mem_filter.mp hv).1

/-- All completion cubes of one active residual-bit slice are disjoint. -/
theorem coreResidualBitSlice_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (T : Finset V) (b : Bool)
    (hactive : ∀ v ∈ T, residualCoord n ∈ active B v) :
    ((coreResidualBitSlice B T b : Finset V) : Set V).PairwiseDisjoint
      (retainedCompletionWords B) := by
  intro u hu v hv huv
  apply residualActiveSlice_pairwiseDisjoint B b
  · have h := Finset.mem_filter.mp hu
    exact (mem_residualActiveSlice B b u).2
      ⟨hactive u h.1, h.2⟩
  · have h := Finset.mem_filter.mp hv
    exact (mem_residualActiveSlice B b v).2
      ⟨hactive v h.1, h.2⟩
  · exact huv

theorem coreResidualBitSlice_union_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (T : Finset V) (b : Bool)
    (hactive : ∀ v ∈ T, residualCoord n ∈ active B v) :
    ((coreResidualBitSlice B T b).biUnion
      (retainedCompletionWords B)).card =
    ∑ v ∈ coreResidualBitSlice B T b,
      (retainedCompletionWords B v).card := by
  classical
  exact Finset.card_biUnion
    (coreResidualBitSlice_pairwiseDisjoint B T b hactive)

/--
Abstract two-slice Hall obstruction inequality:
  sum demand of the opposite side
    > sum (cube size - demand) on the chosen side.

Only the loss-free block identity, local capacity, and within-side
disjointness are used.  Hence this is an actual counting obstruction,
not a further geometric exclusion assumption.
-/
theorem coreResidualBitSlice_opposite_demand_gt_slack
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ)
    {T : Finset V}
    (hdef :
      BlockDeficient (fun v => 2 ^ k v)
        (enlargedProjectedCandidateBlock B k) T)
    (hnoLoss : ∀ v ∈ T, v ∉ projectedLossVertices B k)
    (hactive : ∀ v ∈ T, residualCoord n ∈ active B v)
    (hlocal :
      ∀ v ∈ T, 2 ^ k v ≤ (retainedCompletionWords B v).card)
    (b : Bool) :
    (∑ v ∈ T \ coreResidualBitSlice B T b, 2 ^ k v) >
      ∑ v ∈ coreResidualBitSlice B T b,
        ((retainedCompletionWords B v).card - 2 ^ k v) := by
  classical
  let S := coreResidualBitSlice B T b
  let Q := retainedCompletionWords B
  let d : V → ℕ := fun v => 2 ^ k v
  have hSsub : S ⊆ T := coreResidualBitSlice_subset B T b
  have hBlockUnion :
      T.biUnion (enlargedProjectedCandidateBlock B k) =
        T.biUnion Q := by
    ext word
    constructor
    · intro hw
      obtain ⟨v, hvT, hvWord⟩ := Finset.mem_biUnion.mp hw
      refine Finset.mem_biUnion.mpr ⟨v, hvT, ?_⟩
      rw [enlargedProjectedCandidateBlock_nonloss B k (hnoLoss v hvT)] at hvWord
      exact hvWord
    · intro hw
      obtain ⟨v, hvT, hvWord⟩ := Finset.mem_biUnion.mp hw
      refine Finset.mem_biUnion.mpr ⟨v, hvT, ?_⟩
      rw [enlargedProjectedCandidateBlock_nonloss B k (hnoLoss v hvT)]
      exact hvWord
  have hHall :
      (T.biUnion Q).card < ∑ v ∈ T, d v := by
    unfold BlockDeficient at hdef
    rw [hBlockUnion] at hdef
    exact hdef
  have hSubsetUnion : (S.biUnion Q) ⊆ (T.biUnion Q) := by
    intro word hw
    obtain ⟨v, hv, hvWord⟩ := Finset.mem_biUnion.mp hw
    exact Finset.mem_biUnion.mpr ⟨v, hSsub hv, hvWord⟩
  have hSliceCard :
      (S.biUnion Q).card = ∑ v ∈ S, (Q v).card :=
    coreResidualBitSlice_union_card B T b hactive
  have hCapacity :
      ∀ v ∈ S, d v ≤ (Q v).card := by
    intro v hv
    exact hlocal v (hSsub hv)
  have hSlack :
      (∑ v ∈ S, ((Q v).card - d v)) +
          (∑ v ∈ S, d v) =
        ∑ v ∈ S, (Q v).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    exact Nat.sub_add_cancel (hCapacity v hv)
  have hDecomp : T = S ∪ (T \ S) := by
    ext v
    constructor
    · intro hv
      by_cases hvs : v ∈ S
      · exact Finset.mem_union.mpr (Or.inl hvs)
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_sdiff.mpr ⟨hv, hvs⟩))
    · intro hv
      rcases Finset.mem_union.mp hv with hvs | hvOther
      · exact hSsub hvs
      · exact (Finset.mem_sdiff.mp hvOther).1
  have hDisjoint : Disjoint S (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvOther
    exact (Finset.mem_sdiff.mp hvOther).2 hvS
  have hDemandSplit :
      (∑ v ∈ T, d v) =
        (∑ v ∈ S, d v) + (∑ v ∈ T \ S, d v) := by
    calc
      (∑ v ∈ T, d v) =
          ∑ v ∈ S ∪ (T \ S), d v :=
        congrArg (fun U : Finset V => ∑ v ∈ U, d v) hDecomp
      _ = (∑ v ∈ S, d v) + (∑ v ∈ T \ S, d v) :=
        Finset.sum_union hDisjoint
  have hUnionLe :
      (∑ v ∈ S, (Q v).card) ≤ (T.biUnion Q).card := by
    rw [← hSliceCard]
    exact Finset.card_le_card hSubsetUnion
  change
    (∑ v ∈ T \ S, d v) >
      ∑ v ∈ S, ((Q v).card - d v)
  omega

end OrderedEdgeColoring

namespace DirectionData

open OrderedEdgeColoring

/-- Both residual-bit sides of any genuine loss-free minimal Hall core
satisfy the strict opposite-demand-versus-slack inequality. -/
theorem minimal_loss_free_core_two_sided_slack_pressure
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    {T : Finset V}
    (hdef :
      let B := standardResidualColoring D n (by exact_mod_cast ht)
      let k : V → ℕ := fun i => (cycles i).exponent
      BlockDeficient (fun i => 2 ^ k i)
        (enlargedProjectedCandidateBlock B k) T)
    (hmin :
      let B := standardResidualColoring D n (by exact_mod_cast ht)
      let k : V → ℕ := fun i => (cycles i).exponent
      ∀ U : Finset V, U ⊂ T →
        ¬ BlockDeficient (fun i => 2 ^ k i)
          (enlargedProjectedCandidateBlock B k) U)
    (hnoLoss :
      let B := standardResidualColoring D n (by exact_mod_cast ht)
      let k : V → ℕ := fun i => (cycles i).exponent
      ∀ v ∈ T, v ∉ projectedLossVertices B k) :
    let B := standardResidualColoring D n (by exact_mod_cast ht)
    let k : V → ℕ := fun i => (cycles i).exponent
    ∀ b : Bool,
      (∑ v ∈ T \ coreResidualBitSlice B T b, 2 ^ k v) >
        ∑ v ∈ coreResidualBitSlice B T b,
          ((retainedCompletionWords B v).card - 2 ^ k v) := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  change ∀ b : Bool, (∑ v ∈ T \ coreResidualBitSlice B T b, 2 ^ k v) >
    ∑ v ∈ coreResidualBitSlice B T b,
      ((retainedCompletionWords B v).card - 2 ^ k v)
  have hprof := localCycles_standardResidual_oneLayer_profile D ht cycles
  have hexp : ∀ v, k v ≤ n := hprof.1
  have hone : ∀ v, (active B v).card ≤ n - k v + 1 := hprof.2
  have hactive : ∀ v ∈ T, residualCoord n ∈ active B v :=
    minimal_loss_free_deficient_core_all_residual_active
      D ht cycles hdef hmin hnoLoss
  have hlocal : ∀ v ∈ T,
      2 ^ k v ≤ (retainedCompletionWords B v).card := by
    intro v hv
    have hvNonloss := hnoLoss v hv
    have hup := exponent_le_projectedFree_add_one B k hexp hone v
    have hneq : k v ≠ projectedFree B v + 1 := by
      intro heq
      exact hvNonloss ((mem_projectedLossVertices B k v).2 heq)
    have hle : k v ≤ projectedFree B v := by omega
    exact nonloss_completionBlock_target_le B k hle
  intro b
  exact coreResidualBitSlice_opposite_demand_gt_slack
    B k hdef hnoLoss hactive hlocal b

#print axioms minimal_loss_free_core_two_sided_slack_pressure

end DirectionData
end JSP000404Research
