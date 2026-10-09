import JSP000404Research.FullDyadicExactNonlossBoundaryInterface
import JSP000404Research.DirectionDataHallResidualActiveBoundary
import Mathlib.Tactic

/-!
# G1 reduced to core-internal residual edges at exact non-loss vertices

All vertices in a loss-free minimal Hall-deficient core of genuine
DirectionData have a distinct residual neighbour INSIDE that core.
Therefore G1 needs to exclude only a core-internal residual-edge
configuration through an exact non-loss vertex.

The implication from this sharper open geometric hypothesis to the
previous exact-boundary hypothesis is proved below without sorry.
G2 remains the independent minimal-loss shared-mass exclusion.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open DirectionData

/-- The remaining G1 geometric requirement after core-internal residual
neighbour reduction. No claim is made that arbitrary DirectionData
satisfy it. -/
def LossFreeMinimalHallInternalResidualExactExcluded
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
    ∀ v ∈ T,
      (∃ w ∈ T, w ≠ v ∧
        ((v < w ∧ IsResidual B v w) ∨
         (w < v ∧ IsResidual B w v))) →
      k v ≠ projectedFree B v

/-- All core vertices have internal residual neighbours, so the
refined internal-edge G1 exclusion implies the earlier exact-boundary
exclusion in genuine direction data. -/
theorem minimal_hall_exact_exclusion_of_internal_residual_exclusion
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hInternal :
      LossFreeMinimalHallInternalResidualExactExcluded
        (standardResidualColoring D n (by exact_mod_cast ht))
        (fun i => (cycles i).exponent)) :
    LossFreeMinimalHallExactBoundaryExcluded
      (standardResidualColoring D n (by exact_mod_cast ht))
      (fun i => (cycles i).exponent) := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  intro T hdef hmin hnoLoss v hv
  have hNeighbour :
      ∃ w ∈ T, w ≠ v ∧
        ((v < w ∧ IsResidual B v w) ∨
         (w < v ∧ IsResidual B w v)) :=
    minimal_loss_free_deficient_core_has_internal_residual_neighbor
      D ht cycles hdef hmin hnoLoss v hv
  exact hInternal T hdef hmin hnoLoss v hv hNeighbour

/-- Full abstract n-bit capacity follows conditionally from the sharper G1
internal-residual-edge exclusion and the unchanged G2 geometric exclusion. -/
theorem dyadic_capacity_of_internal_residual_exact_and_shared_mass_exclusions
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hInternal :
      LossFreeMinimalHallInternalResidualExactExcluded
        (standardResidualColoring D n (by exact_mod_cast ht))
        (fun i => (cycles i).exponent))
    (hGeometry :
      MinimalHallLossSharedMassGeometricExclusion
        (standardResidualColoring D n (by exact_mod_cast ht))
        (fun i => (cycles i).exponent)) :
    (∑ i : V, 2 ^ (cycles i).exponent) ≤ 2 ^ n := by
  exact dyadic_capacity_of_exact_nonloss_and_shared_mass_exclusions
    D ht cycles
    (minimal_hall_exact_exclusion_of_internal_residual_exclusion
      D ht cycles hInternal)
    hGeometry

#print axioms minimal_hall_exact_exclusion_of_internal_residual_exclusion
#print axioms dyadic_capacity_of_internal_residual_exact_and_shared_mass_exclusions

end OrderedEdgeColoring
end JSP000404Research
