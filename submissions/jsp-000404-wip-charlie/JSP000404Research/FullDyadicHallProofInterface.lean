import JSP000404Research.DirectionDataMinimalHallObstruction
import JSP000404Research.ResidualEnlargedCandidateHall
import Mathlib.Tactic

/-!
# One explicit outstanding geometry interface for the n-bit dyadic capacity

This file contains NO proof holes.  It connects the complete verified
direction-cycle/Hall chain to exactly two outstanding geometric statements:

1. Every inclusion-minimal deficient enlarged candidate family contains
   at least one genuine projected-loss centre.
2. In a minimal deficient family, geometry forbids the excessive shared
   mass |Q_v| + Delta(T) that the verified deletion arithmetic would force.

The latter is a genuine unsolved geometric assertion, NOT a theorem already
established by the two-exit or pairwise Hall results.  The result below is
conditionally closed; its assumptions must not be described as proved.

This is the LOWER-BRANCH dyadic-capacity interface, not the entire Sendov
classification and not an unconditional JSP-000404 solution.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open DirectionData

/-- Geometry gap A: exclude minimal deficient cores made exclusively
of non-loss centres. -/
def EveryMinimalHallCoreHasProjectedLoss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) : Prop :=
  ∀ T : Finset V,
    BlockDeficient (fun i => 2 ^ k i)
      (enlargedProjectedCandidateBlock B k) T →
    (∀ U : Finset V, U ⊂ T →
      ¬ BlockDeficient (fun i => 2 ^ k i)
        (enlargedProjectedCandidateBlock B k) U) →
    ∃ v ∈ T, v ∈ projectedLossVertices B k

/-- Geometry gap B: rule out the amount of shared Boolean mass
which arithmetic forces at any loss centre of a minimal deficit core.
This is STRICT upper bound, not the already proved lower bound. -/
def MinimalHallLossSharedMassGeometricExclusion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) : Prop :=
  ∀ T : Finset V,
    (hdef : BlockDeficient (fun i => 2 ^ k i)
      (enlargedProjectedCandidateBlock B k) T) →
    (hmin : ∀ U : Finset V, U ⊂ T →
      ¬ BlockDeficient (fun i => 2 ^ k i)
        (enlargedProjectedCandidateBlock B k) U) →
    ∀ v ∈ T, v ∈ projectedLossVertices B k →
      (sharedBlockWords (enlargedProjectedCandidateBlock B k) T v).card <
        (retainedCompletionWords B v).card +
          blockDeficiencyAmount (fun i => 2 ^ k i)
            (enlargedProjectedCandidateBlock B k) T

/-- The complete n-bit capacity proof after TWO explicitly exposed,
currently unproved geometric gaps.  All formal steps after receiving
these hypotheses are verified Lean proof terms, not placeholders. -/
theorem dyadic_capacity_of_minimal_hall_geometric_exclusions
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hLoss :
      EveryMinimalHallCoreHasProjectedLoss
        (standardResidualColoring D n (by exact_mod_cast ht))
        (fun i => (cycles i).exponent))
    (hGeometry :
      MinimalHallLossSharedMassGeometricExclusion
        (standardResidualColoring D n (by exact_mod_cast ht))
        (fun i => (cycles i).exponent)) :
    (∑ i : V, 2 ^ (cycles i).exponent) ≤ 2 ^ n := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  have hExpansion :
      ∀ S : Finset V,
        (∑ i ∈ S, 2 ^ k i) ≤
          (S.biUnion (enlargedProjectedCandidateBlock B k)).card := by
    by_contra hNot
    have hNot' :
        ¬ ∀ S : Finset V,
          (∑ i ∈ S, 2 ^ k i) ≤
            (S.biUnion (enlargedProjectedCandidateBlock B k)).card :=
      hNot
    obtain ⟨T, _hTnonempty, hdef, hmin⟩ :=
      exists_minimal_enlargedCandidate_deficient_core B k hNot'
    obtain ⟨v, hvT, hvLoss⟩ := hLoss T hdef hmin
    have hmass :
        (retainedCompletionWords B v).card +
          blockDeficiencyAmount
            (fun i => 2 ^ k i)
            (enlargedProjectedCandidateBlock B k) T
          ≤
        (sharedBlockWords
          (enlargedProjectedCandidateBlock B k) T v).card :=
      DirectionData.minimal_true_loss_shared_mass_ge_cube_plus_deficit
        D ht cycles hdef hmin hvT hvLoss
    have hgeometric :
        (sharedBlockWords
          (enlargedProjectedCandidateBlock B k) T v).card <
        (retainedCompletionWords B v).card +
          blockDeficiencyAmount
            (fun i => 2 ^ k i)
            (enlargedProjectedCandidateBlock B k) T := by
      exact hGeometry T hdef hmin v hvT hvLoss
    exact (Nat.not_lt_of_ge hmass) hgeometric
  exact exponent_capacity_of_enlargedProjectedCandidate_expansion
    B k hExpansion

#print axioms dyadic_capacity_of_minimal_hall_geometric_exclusions

end OrderedEdgeColoring
end JSP000404Research
