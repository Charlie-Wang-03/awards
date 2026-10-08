import JSP000404Research.DirectionDataMinimalHallObstruction
import JSP000404Research.ProjectionCutLocalCycle
import Mathlib.Tactic

/-!
# True planar canonical centre exponents: quantified minimal Hall loss

In any finite injective planar configuration with a valid angle cap and
normalized projective width 0<t<n+1, a minimal deficient enlarged
Boolean candidate family has a quantitative shared-word obligation.

For each true projected-loss centre v inside the minimal deficient
core T, the number of words in its enlarged candidate block shared
with another core centre is at least

  card(retainedCompletionWords(v)) + HallDeficit(T).

The exponent is genuinely the planar centreExponent, using the
existing projectionCutLocalCycle_exponent_eq_centreExponent theorem.

This does not assume delta<1/2, and does not prove that the required
collisions are geometrically impossible; that remains the all-N gap.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_minimal_loss_shared_mass_ge_cube_plus_deficit
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (htwidth : t < (n : ℝ) + 1)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {T : Finset (ProjectionOrdered V)}
    (hdef :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let D := genericDirectionData_sendov hp hcap htpos hlam
      let B := standardResidualColoring D n
        (by exact_mod_cast htwidth)
      let k : ProjectionOrdered V → ℕ :=
        fun i => centreExponent (cycles i) t
      BlockDeficient (fun i => 2 ^ k i)
        (enlargedProjectedCandidateBlock B k) T)
    (hmin :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let D := genericDirectionData_sendov hp hcap htpos hlam
      let B := standardResidualColoring D n
        (by exact_mod_cast htwidth)
      let k : ProjectionOrdered V → ℕ :=
        fun i => centreExponent (cycles i) t
      ∀ U : Finset (ProjectionOrdered V), U ⊂ T →
        ¬ BlockDeficient (fun i => 2 ^ k i)
          (enlargedProjectedCandidateBlock B k) U)
    {v : ProjectionOrdered V}
    (hvT : v ∈ T)
    (hvLoss :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let D := genericDirectionData_sendov hp hcap htpos hlam
      let B := standardResidualColoring D n
        (by exact_mod_cast htwidth)
      v ∈ projectedLossVertices B
        (fun i => centreExponent (cycles i) t)) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D n
      (by exact_mod_cast htwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    (retainedCompletionWords B v).card +
        blockDeficiencyAmount (fun i => 2 ^ k i)
          (enlargedProjectedCandidateBlock B k) T
      ≤
    (sharedBlockWords (enlargedProjectedCandidateBlock B k) T v).card := by
  classical
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast htwidth)
  let localCycles :
      ∀ j : ProjectionOrdered V, LocalDirectionCycle D j :=
    fun j => projectionCutLocalCycle hp hcap htpos hlam j (cycles j)
  let kLocal : ProjectionOrdered V → ℕ :=
    fun j => (localCycles j).exponent
  let kCanonical : ProjectionOrdered V → ℕ :=
    fun j => centreExponent (cycles j) t
  have hk : kLocal = kCanonical := by
    funext j
    exact projectionCutLocalCycle_exponent_eq_centreExponent
      hp hcap htpos hlam j (cycles j)
  have hdef' :
      BlockDeficient (fun i => 2 ^ kLocal i)
        (enlargedProjectedCandidateBlock B kLocal) T := by
    rw [hk]
    exact hdef
  have hmin' :
      ∀ U : Finset (ProjectionOrdered V), U ⊂ T →
        ¬ BlockDeficient (fun i => 2 ^ kLocal i)
          (enlargedProjectedCandidateBlock B kLocal) U := by
    rw [hk]
    exact hmin
  have hvLoss' : v ∈ projectedLossVertices B kLocal := by
    rw [hk]
    exact hvLoss
  have hquant :
      (retainedCompletionWords B v).card +
        blockDeficiencyAmount (fun i => 2 ^ kLocal i)
          (enlargedProjectedCandidateBlock B kLocal) T
      ≤
      (sharedBlockWords
        (enlargedProjectedCandidateBlock B kLocal) T v).card := by
    exact DirectionData.minimal_true_loss_shared_mass_ge_cube_plus_deficit
      D htwidth localCycles hdef' hmin' hvT hvLoss'
  rw [hk] at hquant
  exact hquant

#print axioms planar_minimal_loss_shared_mass_ge_cube_plus_deficit

end ProjectionOrdered
end JSP000404Research
