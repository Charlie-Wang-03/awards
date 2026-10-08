import JSP000404Research.FullDyadicHallProofInterface
import JSP000404Research.DirectionDataHallExactNonlossReduction
import Mathlib.Tactic

/-!
# Replace geometry gap G1 by the precise exact-nonloss boundary case

Twofold completion multiplicity has already ruled out every deficient
subset consisting solely of strict non-loss centres. Genuine DirectionData
also has the one-layer profile k <= projectedFree + 1.

Thus if a deficient core contains no projected-loss vertex, it MUST
contain an exact non-loss vertex satisfying k = projectedFree.

The refined geometric hypothesis here excludes only that exact non-loss
boundary in a loss-free inclusion-minimal Hall core.  The reduction from
this sharper hypothesis to the original loss-centre-existence condition,
and then to the full n-bit capacity via the separate G2 shared-mass
geometric exclusion, is entirely formalized without sorry.

This does not prove the exact-boundary geometric exclusion itself.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open DirectionData

/-- Refined open geometry gap G1-exact: in a minimal deficient core
containing no projected-loss vertex, there can be no EXACT
non-loss vertex. Strict non-loss vertices need no new geometry. -/
def LossFreeMinimalHallExactBoundaryExcluded
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) : Prop :=
  ∀ T : Finset V,
    (hdef : BlockDeficient (fun i => 2 ^ k i)
      (enlargedProjectedCandidateBlock B k) T) →
    (hmin : ∀ U : Finset V, U ⊂ T →
      ¬ BlockDeficient (fun i => 2 ^ k i)
        (enlargedProjectedCandidateBlock B k) U) →
    (hnoLoss : ∀ v ∈ T, v ∉ projectedLossVertices B k) →
    ∀ v ∈ T, k v ≠ projectedFree B v

/-- The verified exact-or-loss dichotomy discharges the former broad
G1 hypothesis from the exact-nonloss-only geometric exclusion. -/
theorem minimal_hall_core_has_loss_of_exact_boundary_exclusion
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hExact :
      LossFreeMinimalHallExactBoundaryExcluded
        (standardResidualColoring D n (by exact_mod_cast ht))
        (fun i => (cycles i).exponent)) :
    EveryMinimalHallCoreHasProjectedLoss
      (standardResidualColoring D n (by exact_mod_cast ht))
      (fun i => (cycles i).exponent) := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  intro T hdef hmin
  by_contra hno
  have hnoLoss : ∀ v ∈ T, v ∉ projectedLossVertices B k := by
    intro v hv hloss
    exact hno ⟨v, hv, hloss⟩
  obtain ⟨v, hv, _hnLoss, heq⟩ :=
    deficient_loss_free_core_has_exact_nonloss
      D ht cycles hdef hnoLoss
  exact hExact T hdef hmin hnoLoss v hv heq

/-- Conditional dyadic capacity with the strictly localized exact-nonloss
G1 geometry requirement, plus unchanged global shared-mass G2. -/
theorem dyadic_capacity_of_exact_nonloss_and_shared_mass_exclusions
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hExact :
      LossFreeMinimalHallExactBoundaryExcluded
        (standardResidualColoring D n (by exact_mod_cast ht))
        (fun i => (cycles i).exponent))
    (hGeometry :
      MinimalHallLossSharedMassGeometricExclusion
        (standardResidualColoring D n (by exact_mod_cast ht))
        (fun i => (cycles i).exponent)) :
    (∑ i : V, 2 ^ (cycles i).exponent) ≤ 2 ^ n := by
  exact dyadic_capacity_of_minimal_hall_geometric_exclusions
    D ht cycles
    (minimal_hall_core_has_loss_of_exact_boundary_exclusion
      D ht cycles hExact)
    hGeometry

#print axioms minimal_hall_core_has_loss_of_exact_boundary_exclusion
#print axioms dyadic_capacity_of_exact_nonloss_and_shared_mass_exclusions

end OrderedEdgeColoring
end JSP000404Research
