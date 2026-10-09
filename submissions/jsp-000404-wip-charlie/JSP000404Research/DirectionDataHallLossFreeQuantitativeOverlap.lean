import JSP000404Research.DirectionDataHallResidualSlicePressure
import JSP000404Research.MinimalBlockSharedDeficit
import Mathlib.Tactic

/-!
# G1: the full Hall deficit is paid in each loss-free vertex's overlap

Let T be an inclusion-minimal Hall-deficient, loss-free core in actual
DirectionData. Every enlarged candidate block in T equals Q_v, the
retained completion cube.  For each vertex v of T the number of words
shared with the other centres must exceed the *entire* local slack
by at least the actual global Hall deficit Delta(T) > 0.

Unlike just producing one residual neighbour, this is a numerical
obligation for EVERY vertex and locates precisely the cross-slice
overlap that any future geometric G1 contradiction must rule out.

This proof does not close G1, G2, or the original JSP-000404 conjecture.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- In a true loss-free minimal Hall obstruction, every retained cube
must overlap the other retained cubes by at least its local slack
plus the entire global positive Hall deficit. -/
theorem minimal_loss_free_core_each_cube_overlap_pays_full_deficit
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
    ∀ v ∈ T,
      blockDeficiencyAmount (fun i => 2 ^ k i)
          (enlargedProjectedCandidateBlock B k) T
        + ((retainedCompletionWords B v).card - 2 ^ k v)
      ≤ (retainedCompletionWords B v ∩
          ((T.erase v).biUnion (retainedCompletionWords B))).card := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  change ∀ v ∈ T,
      blockDeficiencyAmount (fun i => 2 ^ k i)
          (enlargedProjectedCandidateBlock B k) T
        + ((retainedCompletionWords B v).card - 2 ^ k v)
      ≤ (retainedCompletionWords B v ∩
          ((T.erase v).biUnion (retainedCompletionWords B))).card
  have hprof := localCycles_standardResidual_oneLayer_profile D ht cycles
  have hexp : ∀ v, k v ≤ n := hprof.1
  have hone : ∀ v, (active B v).card ≤ n - k v + 1 := hprof.2
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
  have hblocks : ∀ v ∈ T,
      enlargedProjectedCandidateBlock B k v = retainedCompletionWords B v := by
    intro v hv
    exact enlargedProjectedCandidateBlock_nonloss B k (hnoLoss v hv)
  intro v hvT
  have hother :
      (T.erase v).biUnion (enlargedProjectedCandidateBlock B k) =
      (T.erase v).biUnion (retainedCompletionWords B) := by
    ext word
    constructor
    · intro hw
      obtain ⟨w, hw, hwWord⟩ := Finset.mem_biUnion.mp hw
      have hwT := (Finset.mem_erase.mp hw).2
      apply Finset.mem_biUnion.mpr
      exact ⟨w, hw, (hblocks w hwT) ▸ hwWord⟩
    · intro hw
      obtain ⟨w, hw, hwWord⟩ := Finset.mem_biUnion.mp hw
      have hwT := (Finset.mem_erase.mp hw).2
      apply Finset.mem_biUnion.mpr
      exact ⟨w, hw, (hblocks w hwT).symm ▸ hwWord⟩
  have hshared :
      sharedBlockWords (enlargedProjectedCandidateBlock B k) T v =
        retainedCompletionWords B v ∩
          ((T.erase v).biUnion (retainedCompletionWords B)) := by
    unfold sharedBlockWords
    rw [hblocks v hvT, hother]
  have hvLocal :
      2 ^ k v ≤ (enlargedProjectedCandidateBlock B k v).card := by
    rw [hblocks v hvT]
    exact hlocal v hvT
  have hbound := minimal_deficient_amount_le_shared_excess
    (fun i : V => 2 ^ k i) (enlargedProjectedCandidateBlock B k)
    hdef hmin hvT hvLocal
  rw [hblocks v hvT, hshared] at hbound
  exact hbound

#print axioms minimal_loss_free_core_each_cube_overlap_pays_full_deficit

end DirectionData
end JSP000404Research
