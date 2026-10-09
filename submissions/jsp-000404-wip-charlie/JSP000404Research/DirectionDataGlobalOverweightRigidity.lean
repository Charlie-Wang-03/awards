import JSP000404Research.DirectionDataHallExactCycleTight
import JSP000404Research.ExactProjectedLossIffTightInactive
import JSP000404Research.ResidualOverlapSlackPayment
import JSP000404Research.ResidualCompletionAccounting
import Mathlib.Tactic

/-!
# Genuine global-overweight obstruction: a tight local cycle is necessary

This argument bypasses the formally refuted subset-wise Hall G1
assumption. Global completion mass is controlled without Hall expansion.

At any actual DirectionData one-layer profile:
  * residual-active vertices have exponent <= projectedFree;
  * every vertex has exponent <= projectedFree+1.

When there is no projected-loss centre and no exact projected-saturated
residual-active centre, ALL vertices have k<=projectedFree, and each
residual-active vertex is strictly below projectedFree. Then all completion
overlap is paid by global profile surplus (the strict-slice lemma), and
profile loss is zero. The exact completion identity yields the n-bit bound.

Consequently any overweight data require EITHER a projected-loss centre
with its proved short consecutive-ratio band crossing, OR a residual-active
exact-saturated centre with proved equality in every interior gap step.

This is a necessary structural condition, NOT a proof these centres are
impossible. Both cases are allowed; the 3-point abstract counterexample
saturates the global capacity without violating this necessary condition.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Overweight requires a projected loss or exact residual-active saturation.
This global assertion does not invoke or imply subset-Hall expansion. -/
theorem overweight_forces_loss_or_residual_saturation
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ)
    (hone : ∀ v, k v ≤ projectedFree C v + 1)
    (hresBudget :
      ∀ v, residualCoord n ∈ active C v →
        k v ≤ projectedFree C v)
    (hover : 2 ^ n < ∑ v, 2 ^ k v) :
    (∃ v, v ∈ projectedLossVertices C k) ∨
      (∃ v, residualCoord n ∈ active C v ∧
        k v = projectedFree C v) := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨hnoLoss, hnotSaturated⟩ := h
  have hle : ∀ v, k v ≤ projectedFree C v := by
    intro v
    have hnotEq : k v ≠ projectedFree C v + 1 := by
      intro heq
      exact hnoLoss v ((mem_projectedLossVertices C k v).2 heq)
    have hv := hone v
    omega
  have hzero : totalDyadicProfileLoss k (projectedFree C) = 0 := by
    unfold totalDyadicProfileLoss
    apply Finset.sum_eq_zero
    intro v hv
    have hpow :
        2 ^ k v ≤ 2 ^ projectedFree C v :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (hle v)
    simp [dyadicProfileLoss, Nat.sub_eq_zero_of_le hpow]
  have hnotSat :
      ∀ v, residualCoord n ∈ active C v →
        k v ≠ projectedFree C v := by
    intro v hres
    exact hnotSaturated v hres
  have hpaid :=
    overlap_le_totalSurplus_of_no_saturated_residualActive
      C k hresBudget hnotSat
  have hpay :
      (overlapCompletionWords C).card +
        totalDyadicProfileLoss k (projectedFree C) ≤
        (2 ^ n - (coveredCompletionWords C).card) +
          totalDyadicProfileSurplus k (projectedFree C) := by
    rw [hzero]
    omega
  have hcap :=
    exponent_capacity_of_completion_defect_payment C k hpay
  omega

#print axioms overweight_forces_loss_or_residual_saturation

end OrderedEdgeColoring

namespace DirectionData

open OrderedEdgeColoring

/-- Any overweight genuine DirectionData profile has one of two
specific local geometric obstructions: a short adjacent-ray band
crossing at a loss centre, or completely tight interior/wrap gaps
at an active exact-saturated centre. -/
theorem overweight_directionData_has_rigid_local_witness
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ (cycles i).exponent) :
    (
      ∃ (i : V), ∃ (u v : OtherVertex i)
        (pre post : List (OtherVertex i)),
        (cycles i).rays = pre ++ u :: v :: post ∧
        0 ≤ D.localDirectionValue i v - D.localDirectionValue i u ∧
        D.localDirectionValue i v - D.localDirectionValue i u < 1 ∧
        Nat.floor (D.localDirectionValue i v) -
          Nat.floor (D.localDirectionValue i u) = 1
    ) ∨
    (
      ∃ i : V, ∃ a : ℝ, ∃ xs : List ℝ,
        (cycles i).values = a :: xs ∧
        InteriorBandGapTight a xs ∧
        excess (Nat.floor (a + t - xs.getLastD a)) =
          n - Nat.floor (xs.getLastD a) + Nat.floor a
    ) := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  have hprof := localCycles_standardResidual_oneLayer_profile D ht cycles
  have hexp : ∀ v, k v ≤ n := hprof.1
  have honeActive :
      ∀ v, (active B v).card ≤ n - k v + 1 := hprof.2
  have hone :
      ∀ v, k v ≤ projectedFree B v + 1 :=
    exponent_le_projectedFree_add_one B k hexp honeActive
  have hresBudget :
      ∀ v, residualCoord n ∈ active B v →
        k v ≤ projectedFree B v := by
    intro v hvRes
    have hdrop :=
      retainedActive_card_add_one_le_active_of_residual_mem
        B v hvRes
    have hvBound := honeActive v
    have hvCard :
        (retainedActive B v).card ≤ n := by
      simpa using Finset.card_le_univ (retainedActive B v)
    dsimp [projectedFree]
    omega
  have hob :
      2 ^ n < ∑ i : V, 2 ^ k i := hover
  rcases overweight_forces_loss_or_residual_saturation
      B k hone hresBudget hob with hloss | hsat
  · obtain ⟨i, hiLoss⟩ := hloss
    obtain ⟨u, v, pre, post, hwords, hnonneg, hshort, hband⟩ :=
      projected_loss_has_consecutive_short_band_crossing_rays
        D ht cycles i hiLoss
    exact Or.inl ⟨i, u, v, pre, post,
      hwords, hnonneg, hshort, hband⟩
  · obtain ⟨i, hiRes, hiSat⟩ := hsat
    obtain ⟨a, xs, hvalues, hstep, hwrap⟩ :=
      exact_nonloss_residual_active_local_cycle_rigid
        D ht cycles i hiSat hiRes
    exact Or.inr ⟨i, a, xs, hvalues, hstep, hwrap⟩

#print axioms overweight_directionData_has_rigid_local_witness

end DirectionData
end JSP000404Research
