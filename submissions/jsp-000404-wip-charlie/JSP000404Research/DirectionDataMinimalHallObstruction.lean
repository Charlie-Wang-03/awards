import JSP000404Research.DirectionDataLossNoTwoVertexHall
import JSP000404Research.MinimalHallLossCollisionBranch
import JSP000404Research.MinimalHallLossDefectMass
import Mathlib.Tactic

/-!
# Genuine direction-data minimal Hall obstructions: mass and branching

The two abstract minimal-deficiency statements are specialized to
the actual standard residual n-bit colouring for any valid direction
data of width t<n+1, using only the local-cycle budget and the
phase-slip rigidity at an exact projected-loss centre.

No separate hypothesis that ALL local exponents are < n is imposed.
At the loss centre strictness follows from the two adjacent retained
active bands. At every other centre the one-layer bounds follow from
the complete, nonempty local direction cycles.

At a minimal deficient core T and each true loss centre v in T:

* its enlarged-block shared mass is at least one whole loss cube
  PLUS the entire weighted Hall deficit of T;
* it collides either with another loss centre or with two distinct
  non-loss centres.

Neither conclusion alone implies global weighted Hall expansion.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

theorem minimal_true_loss_shared_mass_ge_cube_plus_deficit
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
    {v : V}
    (hvT : v ∈ T)
    (hvLoss :
      v ∈ projectedLossVertices
        (standardResidualColoring D n (by exact_mod_cast ht))
        (fun i => (cycles i).exponent)) :
    let B := standardResidualColoring D n (by exact_mod_cast ht)
    let k : V → ℕ := fun i => (cycles i).exponent
    (retainedCompletionWords B v).card +
      blockDeficiencyAmount (fun i => 2 ^ k i)
        (enlargedProjectedCandidateBlock B k) T
      ≤
    (sharedBlockWords (enlargedProjectedCandidateBlock B k) T v).card := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  have hvLt : k v < n :=
    projected_loss_exponent_lt_n D ht cycles v hvLoss
  exact minimal_loss_shared_card_ge_cube_add_deficit
    B k hdef hmin hvT hvLoss hvLt

theorem minimal_true_loss_neighbour_or_two_nonloss
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
    {v : V}
    (hvT : v ∈ T)
    (hvLoss :
      v ∈ projectedLossVertices
        (standardResidualColoring D n (by exact_mod_cast ht))
        (fun i => (cycles i).exponent)) :
    let B := standardResidualColoring D n (by exact_mod_cast ht)
    let k : V → ℕ := fun i => (cycles i).exponent
    (∃ w : V, w ∈ T ∧ w ≠ v ∧
       w ∈ projectedLossVertices B k ∧
       (enlargedProjectedCandidateBlock B k v ∩
         enlargedProjectedCandidateBlock B k w).Nonempty)
    ∨
    (∃ w z : V, w ∈ T ∧ z ∈ T ∧
       w ≠ v ∧ z ≠ v ∧ w ≠ z ∧
       w ∉ projectedLossVertices B k ∧
       z ∉ projectedLossVertices B k ∧
       (enlargedProjectedCandidateBlock B k v ∩
         enlargedProjectedCandidateBlock B k w).Nonempty ∧
       (enlargedProjectedCandidateBlock B k v ∩
         enlargedProjectedCandidateBlock B k z).Nonempty) := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  have hprofile :=
    localCycles_standardResidual_oneLayer_profile D ht cycles
  have hexp : ∀ i, k i ≤ n := hprofile.1
  have hone :
      ∀ i, (active B i).card ≤ n - k i + 1 := hprofile.2
  have hvLt : k v < n :=
    projected_loss_exponent_lt_n D ht cycles v hvLoss
  exact minimal_loss_neighbour_is_loss_or_two_nonloss
    B k hexp hone hdef hmin hvT hvLoss hvLt

#print axioms minimal_true_loss_shared_mass_ge_cube_plus_deficit
#print axioms minimal_true_loss_neighbour_or_two_nonloss

end DirectionData
end JSP000404Research
