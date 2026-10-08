import JSP000404Research.PlanarPhaseSlipTriangleParity
import JSP000404Research.ResidualCompletionAccounting
import Mathlib.Tactic

/-!
# Exact Boolean completion deficit for genuine planar centre exponents

The planar generic projection constructs a coherent (n+1)-colour
ordered edge colouring, while each canonical centre cycle gives the
actual exponent of the original planar angular problem.

The existing completion accounting is now specialized *without a
global capacity assumption* to precisely these canonical exponents.
The retained Boolean cube has exact covering/overlap accounting:
  targetMass + surplus = coveredMass + overlapMass + profileLoss.

Consequently any hypothetical overweight planar configuration yields
a strictly unpaid completion deficit:
  holes + surplus < overlaps + loss.

This does not rule out such a deficit: proving the reverse inequality
from actual planar geometry remains the central unsolved step.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open DirectionData
open OrderedEdgeColoring
open scoped BigOperators

/-- Exact global Boolean-hole/overlap accounting for the actual
canonical projective centre exponents of an injective planar
configuration satisfying the angle cap. -/
theorem planar_canonical_completion_mass_balance
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
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D n
      (by exact_mod_cast htwidth)
    let exponent : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    let free : ProjectionOrdered V → ℕ :=
      fun i => n - (retainedActive B i).card
    (∑ i : ProjectionOrdered V, 2 ^ exponent i) +
        totalDyadicProfileSurplus exponent free =
      (coveredCompletionWords B).card +
        (overlapCompletionWords B).card +
        totalDyadicProfileLoss exponent free := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  dsimp
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring
      (genericDirectionData_sendov hp hcap htpos hlam)
      n (by exact_mod_cast htwidth)
  let exponent : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  let free : ProjectionOrdered V → ℕ :=
    fun i => n - (retainedActive B i).card
  change (∑ i : ProjectionOrdered V, 2 ^ exponent i) +
      totalDyadicProfileSurplus exponent free =
    (coveredCompletionWords B).card +
      (overlapCompletionWords B).card +
      totalDyadicProfileLoss exponent free
  exact residual_projection_accounting_balance
    exponent free (coveredCompletionWords B).card
    (overlapCompletionWords B).card
    (projectedFree_mass_eq_covered_add_overlap B)

/-- A counterexample to the target n-bit weighted capacity would have
strictly more Boolean overlap plus profile loss than available holes
and profile surplus. This is an exact, unconditional consequence of
the geometric-to-Boolean representation, not an impossibility proof. -/
theorem planar_overweight_forces_unpaid_completion_defect
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
    (hover :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      2 ^ n <
        ∑ i : ProjectionOrdered V,
          2 ^ centreExponent (cycles i) t) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D n
      (by exact_mod_cast htwidth)
    let exponent : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    let free : ProjectionOrdered V → ℕ :=
      fun i => n - (retainedActive B i).card
    (2 ^ n - (coveredCompletionWords B).card) +
        totalDyadicProfileSurplus exponent free <
      (overlapCompletionWords B).card +
        totalDyadicProfileLoss exponent free := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  dsimp
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring
      (genericDirectionData_sendov hp hcap htpos hlam)
      n (by exact_mod_cast htwidth)
  let exponent : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  let free : ProjectionOrdered V → ℕ :=
    fun i => n - (retainedActive B i).card
  change (2 ^ n - (coveredCompletionWords B).card) +
      totalDyadicProfileSurplus exponent free <
    (overlapCompletionWords B).card +
      totalDyadicProfileLoss exponent free
  have hcovered := coveredCompletionWords_card_le_two_pow B
  have hmass : (∑ i : ProjectionOrdered V, 2 ^ exponent i) +
      totalDyadicProfileSurplus exponent free =
    (coveredCompletionWords B).card +
      (overlapCompletionWords B).card +
      totalDyadicProfileLoss exponent free :=
    residual_projection_accounting_balance
      exponent free (coveredCompletionWords B).card
      (overlapCompletionWords B).card
      (projectedFree_mass_eq_covered_add_overlap B)
  have hover' : 2 ^ n <
      ∑ i : ProjectionOrdered V, 2 ^ exponent i := by
    simpa [exponent] using hover
  omega

#print axioms planar_canonical_completion_mass_balance
#print axioms planar_overweight_forces_unpaid_completion_defect

end ProjectionOrdered
end JSP000404Research
