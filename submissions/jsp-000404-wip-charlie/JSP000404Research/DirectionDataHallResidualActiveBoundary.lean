import JSP000404Research.DirectionDataHallExactNonlossReduction
import JSP000404Research.MinimalBlockSharedDeficit
import JSP000404Research.ResidualCompletionMultiplicity
import Mathlib.Tactic

/-!
# G1: loss-free Hall obstructions require a residual-active exact boundary

The strict non-loss subset Hall theorem has already excluded deficient sets
whose every vertex has exponent strictly below its projected free dimension.
The one-layer direction-data profile then forces a loss-free deficient core
to contain an exact non-loss vertex.

Here we use inclusion-minimality to prove an additional, unconditional
restriction: an exact non-loss vertex in a loss-free minimal deficient core
MUST be incident to a residual edge. Otherwise its retained completion
cube is private and the exact local demand is paid in full.

Thus the still-open G1 geometry question concerns only
  exponent(v) = projectedFree(v)
AND
  residualCoord is active at v.
This is an actual narrowing of G1, not a proof of the global Hall theorem.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- If a genuine direction-data core is inclusion-minimal, Hall-deficient,
and loss-free, some exact non-loss centre is incident to a residual edge.
All hypotheses refer to the canonical (n+1)-colour direction system. -/
theorem minimal_loss_free_deficient_core_has_residual_active_exact_nonloss
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
    ∃ v ∈ T,
      k v = projectedFree B v ∧
      residualCoord n ∈ active B v := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  obtain ⟨v, hvT, hvNonloss, hvExact⟩ :=
    deficient_loss_free_core_has_exact_nonloss
      D ht cycles hdef hnoLoss
  have hvBlock :
      (enlargedProjectedCandidateBlock B k v).card = 2 ^ k v := by
    rw [enlargedProjectedCandidateBlock_nonloss B k hvNonloss,
      retainedCompletionWords_card, ← hvExact]
  obtain ⟨word, hword⟩ :=
    minimal_deficient_exact_block_has_shared_word
      (fun i : V => 2 ^ k i)
      (enlargedProjectedCandidateBlock B k)
      hdef hmin hvT hvBlock
  obtain ⟨hvWord, hother⟩ := Finset.mem_inter.mp hword
  obtain ⟨w, hwErase, hwWord⟩ := Finset.mem_biUnion.mp hother
  have hwT : w ∈ T := (Finset.mem_erase.mp hwErase).2
  have hwNe : w ≠ v := (Finset.mem_erase.mp hwErase).1
  have hwNonloss : w ∉ projectedLossVertices B k :=
    hnoLoss w hwT
  rw [enlargedProjectedCandidateBlock_nonloss B k hvNonloss] at hvWord
  rw [enlargedProjectedCandidateBlock_nonloss B k hwNonloss] at hwWord
  have hvActive : residualCoord n ∈ active B v := by
    rcases retainedCompletion_overlap_forces_residual
      B (Ne.symm hwNe) hvWord hwWord with
      ⟨hvw, hres⟩ | ⟨hwv, hres⟩
    · exact (residualCoord_mem_active_of_isResidual B hvw hres).1
    · exact (residualCoord_mem_active_of_isResidual B hwv hres).2
  exact ⟨v, hvT, hvExact, hvActive⟩

/--
Every vertex (not only an exact-boundary witness) in a loss-free,
inclusion-minimal deficient core has an INTERNAL residual-edge neighbour.

Proof: the true one-layer profile supplies local capacity at each non-loss
vertex; minimal Hall deficiency therefore forces that vertex's candidate
block to share a word. Since both endpoints are non-loss, the shared word
belongs to both retained completion cubes. The previously proved
two-carrier rigidity makes their connecting edge residual.
-/
theorem minimal_loss_free_deficient_core_has_internal_residual_neighbor
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
    ∀ v ∈ T, ∃ w ∈ T, w ≠ v ∧
      ((v < w ∧ IsResidual B v w) ∨
       (w < v ∧ IsResidual B w v)) := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  have hprofile :=
    localCycles_standardResidual_oneLayer_profile D ht cycles
  have hexp : ∀ x, k x ≤ n := hprofile.1
  have hone : ∀ x, (active B x).card ≤ n - k x + 1 := hprofile.2
  intro v hvT
  have hvNonloss : v ∉ projectedLossVertices B k :=
    hnoLoss v hvT
  have hvUpper : k v ≤ projectedFree B v + 1 :=
    exponent_le_projectedFree_add_one B k hexp hone v
  have hvNotLoss : k v ≠ projectedFree B v + 1 := by
    intro heq
    exact hvNonloss ((mem_projectedLossVertices B k v).2 heq)
  have hvLe : k v ≤ projectedFree B v := by omega
  have hvLocal :
      2 ^ k v ≤ (enlargedProjectedCandidateBlock B k v).card := by
    rw [enlargedProjectedCandidateBlock_nonloss B k hvNonloss]
    exact nonloss_completionBlock_target_le B k hvLe
  obtain ⟨word, hvWord, hother⟩ :=
    minimal_deficient_block_has_collision_of_local_capacity
      (fun i : V => 2 ^ k i)
      (enlargedProjectedCandidateBlock B k)
      hdef hmin hvT hvLocal
  obtain ⟨w, hwErase, hwWord⟩ := Finset.mem_biUnion.mp hother
  have hwT : w ∈ T := (Finset.mem_erase.mp hwErase).2
  have hwNe : w ≠ v := (Finset.mem_erase.mp hwErase).1
  have hwNonloss : w ∉ projectedLossVertices B k :=
    hnoLoss w hwT
  rw [enlargedProjectedCandidateBlock_nonloss B k hvNonloss] at hvWord
  rw [enlargedProjectedCandidateBlock_nonloss B k hwNonloss] at hwWord
  have hres := retainedCompletion_overlap_forces_residual
    B (Ne.symm hwNe) hvWord hwWord
  exact ⟨w, hwT, hwNe, hres⟩

/--
The core-internal residual neighbour of each vertex also implies that the
residual coordinate is active there.  No new geometric assumptions.
-/
theorem minimal_loss_free_deficient_core_all_residual_active
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
    ∀ v ∈ T, residualCoord n ∈ active B v := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  intro v hvT
  obtain ⟨w, _hwT, _hwNe, hres⟩ :=
    minimal_loss_free_deficient_core_has_internal_residual_neighbor
      D ht cycles hdef hmin hnoLoss v hvT
  rcases hres with ⟨hvw, hr⟩ | ⟨hwv, hr⟩
  · exact (residualCoord_mem_active_of_isResidual B hvw hr).1
  · exact (residualCoord_mem_active_of_isResidual B hwv hr).2

/--
A loss-free minimal deficient Hall core must meet BOTH residual bit
polarities.  Indeed every vertex has a core-internal residual neighbour;
the lower and upper endpoints of such an edge have residual bits false
and true, respectively.  This is a structural reduction to a genuine
two-sided collision problem, not a proof of G1 itself.
-/
theorem minimal_loss_free_deficient_core_has_both_residual_polarities
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
    ∃ u ∈ T, ∃ v ∈ T,
      u < v ∧
      bit B u (residualCoord n) = false ∧
      bit B v (residualCoord n) = true := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  have hnonempty : T.Nonempty :=
    deficient_set_nonempty_of_positive_demands
      (fun i : V => 2 ^ k i)
      (enlargedProjectedCandidateBlock B k)
      (fun i => by positivity)
      hdef
  obtain ⟨a, ha⟩ := hnonempty
  obtain ⟨b, hb, _habNe, horient⟩ :=
    minimal_loss_free_deficient_core_has_internal_residual_neighbor
      D ht cycles hdef hmin hnoLoss a ha
  rcases horient with ⟨hab, hres⟩ | ⟨hba, hres⟩
  · have hcol : B.color a b = residualCoord n := by
      apply Fin.ext
      simpa [residualCoord] using residual_val_eq B hres
    have hfalse := edgeColor_bit_lower_eq_false B hab
    have htrue := edgeColor_bit_upper_eq_true B hab
    rw [hcol] at hfalse htrue
    exact ⟨a, ha, b, hb, hab, hfalse, htrue⟩
  · have hcol : B.color b a = residualCoord n := by
      apply Fin.ext
      simpa [residualCoord] using residual_val_eq B hres
    have hfalse := edgeColor_bit_lower_eq_false B hba
    have htrue := edgeColor_bit_upper_eq_true B hba
    rw [hcol] at hfalse htrue
    exact ⟨b, hb, a, ha, hba, hfalse, htrue⟩

#print axioms minimal_loss_free_deficient_core_has_residual_active_exact_nonloss
#print axioms minimal_loss_free_deficient_core_has_both_residual_polarities
#print axioms minimal_loss_free_deficient_core_has_internal_residual_neighbor
#print axioms minimal_loss_free_deficient_core_all_residual_active

end DirectionData
end JSP000404Research
