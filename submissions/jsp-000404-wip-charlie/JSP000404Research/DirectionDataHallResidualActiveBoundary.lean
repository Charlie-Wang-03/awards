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

#print axioms minimal_loss_free_deficient_core_has_residual_active_exact_nonloss

end DirectionData
end JSP000404Research
