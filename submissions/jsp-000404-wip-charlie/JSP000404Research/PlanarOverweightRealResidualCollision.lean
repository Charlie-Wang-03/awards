import JSP000404Research.DirectionDataOverweightRealResidualCollision
import JSP000404Research.ProjectionCutLocalCycle
import Mathlib.Tactic

/-!
# Planar lifting: an overweight canonical configuration has genuine hard geometry

The general residual completion accounting forces either a projected-loss
centre or a real residual edge whose two retained completion cubes overlap
and whose carrier has an exactly projected-saturated endpoint.

We transfer this dichotomy to the ACTUAL planar centre projective exponents
through the kernel-checked projection-cut local-cycle representation.

It does NOT assume universal subset Hall expansion (the old false G1).
The geometric task is to globally compensate these concrete hard carriers
and loss centres, not to rule out isolated locally saturated centres.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open DirectionData
open OrderedEdgeColoring

/-- For a genuine injective planar AngleCap configuration, excess dyadic
mass forces either an actual projected-loss centre or an actual shared
Boolean completion word carried by a residual edge with a saturated end. -/
theorem planar_overweight_has_loss_or_real_saturated_residual_collision
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (hwidth : t < (n : ℝ) + 1)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hover :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      2 ^ n < ∑ i : ProjectionOrdered V,
        2 ^ centreExponent (cycles i) t) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D n
      (by exact_mod_cast hwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    (∃ i : ProjectionOrdered V,
      i ∈ projectedLossVertices B k) ∨
      (∃ (u v : ProjectionOrdered V) (word : Fin n → Bool),
        u < v ∧
        IsResidual B u v ∧
        word ∈ retainedCompletionWords B u ∧
        word ∈ retainedCompletionWords B v ∧
        (k u = projectedFree B u ∨
          k v = projectedFree B v)) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  let D : DirectionData (ProjectionOrdered V) t :=
    genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let L : ∀ i : ProjectionOrdered V, LocalDirectionCycle D i :=
    fun i => projectionCutLocalCycle hp hcap htpos hlam i (cycles i)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  change (∃ i : ProjectionOrdered V,
    i ∈ projectedLossVertices B k) ∨
      (∃ (u v : ProjectionOrdered V) (word : Fin n → Bool),
        u < v ∧ IsResidual B u v ∧
        word ∈ retainedCompletionWords B u ∧
        word ∈ retainedCompletionWords B v ∧
        (k u = projectedFree B u ∨ k v = projectedFree B v))
  have hexp :
      ∀ i : ProjectionOrdered V,
        (L i).exponent = k i := by
    intro i
    exact projectionCutLocalCycle_exponent_eq_centreExponent
      hp hcap htpos hlam i (cycles i)
  have hlocalOverweight :
      2 ^ n < ∑ i : ProjectionOrdered V, 2 ^ (L i).exponent := by
    calc
      2 ^ n < ∑ i : ProjectionOrdered V,
          2 ^ centreExponent (cycles i) t := hover
      _ = ∑ i : ProjectionOrdered V, 2 ^ (L i).exponent := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hexp i]
  have hcase :=
    overweight_directionData_has_real_saturated_residual_collision
      D hwidth L hlocalOverweight
  change (∃ i : ProjectionOrdered V,
    i ∈ projectedLossVertices B
      (fun j => (L j).exponent)) ∨
      (∃ (u v : ProjectionOrdered V) (word : Fin n → Bool),
        u < v ∧ IsResidual B u v ∧
        word ∈ retainedCompletionWords B u ∧
        word ∈ retainedCompletionWords B v ∧
        ((L u).exponent = projectedFree B u ∨
          (L v).exponent = projectedFree B v)) at hcase
  have hk : (fun i : ProjectionOrdered V => (L i).exponent) = k := by
    funext i
    exact hexp i
  rw [hk] at hcase
  simpa only [hexp] using hcase

#print axioms planar_overweight_has_loss_or_real_saturated_residual_collision

end ProjectionOrdered
end JSP000404Research
