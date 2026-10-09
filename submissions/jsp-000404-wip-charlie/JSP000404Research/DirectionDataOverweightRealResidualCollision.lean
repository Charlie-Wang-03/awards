import JSP000404Research.ResidualHardRemainderExactCredit
import JSP000404Research.DirectionDataGlobalOverweightRigidity
import Mathlib.Tactic

/-!
# Overweight forces a REAL saturated residual collision or projected loss

The previously derived overweight rigidity guarantees a locally saturated
residual-active centre, but such a centre could be isolated from all
completion overlap. The exact hard-remainder identity strengthens this.

If an overweight colouring has no projected-loss vertex, the profile loss
mass vanishes. Its globally unpayable hard remainder is necessarily
nonempty. Every hard overlap word is carried by a genuine residual edge
u<v with a shared retained Boolean completion word, and at least one
projected-saturated endpoint.

The witness therefore certifies an ACTUAL overlap, not merely a
potential local saturation. This follows without the false subset-Hall G1.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Overweight can be localized to either an actual profile-loss centre
or a residual edge with a shared hard-completion word and at least one
exact projected-saturated endpoint. -/
theorem overweight_forces_loss_or_saturated_residual_collision
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ)
    (hexp : ∀ v, k v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - k v + 1)
    (hover : 2 ^ n < ∑ v : V, 2 ^ k v) :
    (∃ v : V, v ∈ projectedLossVertices C k) ∨
      (∃ (u v : V) (word : Fin n → Bool),
        u < v ∧
        IsResidual C u v ∧
        word ∈ retainedCompletionWords C u ∧
        word ∈ retainedCompletionWords C v ∧
        (k u = projectedFree C u ∨
          k v = projectedFree C v)) := by
  classical
  by_cases hloss : ∃ v : V, v ∈ projectedLossVertices C k
  · exact Or.inl hloss
  · right
    have hnoLoss : ∀ v : V,
        v ∉ projectedLossVertices C k := by
      intro v hv
      exact hloss ⟨v, hv⟩
    have hone :
        ∀ v : V, k v ≤ projectedFree C v + 1 :=
      exponent_le_projectedFree_add_one C k hexp honeLoss
    have hle : ∀ v : V, k v ≤ projectedFree C v := by
      intro v
      have hne : k v ≠ projectedFree C v + 1 := by
        intro heq
        exact hnoLoss v
          ((mem_projectedLossVertices C k v).2 heq)
      have hv := hone v
      omega
    have hzero :
        totalDyadicProfileLoss k (projectedFree C) = 0 := by
      unfold totalDyadicProfileLoss
      apply Finset.sum_eq_zero
      intro v hv
      have hp :
          2 ^ k v ≤ 2 ^ projectedFree C v :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (hle v)
      simp [dyadicProfileLoss, Nat.sub_eq_zero_of_le hp]
    have hhard :=
      overweight_forces_unpaid_exact_hard_remainder C k hover
    rw [hzero] at hhard
    have hpositive :
        0 < (saturatedOverlapWords C k).card := by
      omega
    obtain ⟨word, hword⟩ :=
      Finset.card_pos.mp hpositive
    obtain ⟨u, v, huv, hres, huWord, hvWord, hsat⟩ :=
      saturatedOverlapWord_has_saturated_carrier
        C k hexp honeLoss hword
    exact ⟨u, v, word, huv, hres, huWord, hvWord, hsat⟩

#print axioms overweight_forces_loss_or_saturated_residual_collision

end OrderedEdgeColoring

namespace DirectionData

open OrderedEdgeColoring

/-- Genuine DirectionData version: any overweight configuration carries
a profile-loss centre or an actual saturated residual collision. -/
theorem overweight_directionData_has_real_saturated_residual_collision
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hover : 2 ^ n < ∑ i : V, 2 ^ (cycles i).exponent) :
    let B := standardResidualColoring D n (by exact_mod_cast ht)
    let k : V → ℕ := fun i => (cycles i).exponent
    (∃ v : V, v ∈ projectedLossVertices B k) ∨
      (∃ (u v : V) (word : Fin n → Bool),
        u < v ∧
        IsResidual B u v ∧
        word ∈ retainedCompletionWords B u ∧
        word ∈ retainedCompletionWords B v ∧
        (k u = projectedFree B u ∨
          k v = projectedFree B v)) := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  change (∃ v : V, v ∈ projectedLossVertices B k) ∨
    (∃ (u v : V) (word : Fin n → Bool),
      u < v ∧ IsResidual B u v ∧
      word ∈ retainedCompletionWords B u ∧
      word ∈ retainedCompletionWords B v ∧
      (k u = projectedFree B u ∨
        k v = projectedFree B v))
  have hprof :=
    localCycles_standardResidual_oneLayer_profile D ht cycles
  have hexp : ∀ v, k v ≤ n := hprof.1
  have honeLoss :
      ∀ v, (active B v).card ≤ n - k v + 1 := hprof.2
  exact overweight_forces_loss_or_saturated_residual_collision
    B k hexp honeLoss hover

#print axioms overweight_directionData_has_real_saturated_residual_collision

end DirectionData
end JSP000404Research
