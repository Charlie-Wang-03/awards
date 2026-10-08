import JSP000404Research.ProjectedLossTwoExitNoHalfThreshold
import JSP000404Research.ProjectionCutLocalCycle
import Mathlib.Tactic

/-!
# Every genuine planar projected-loss cube has two disjoint flip exits

This specializes the general DirectionData loss classification and two-exit
theorem to the *canonical projective centre exponents* of a finite,
injective planar point configuration.

The crucial equality is not assumed: the established
projectionCutLocalCycle_exponent_eq_centreExponent representation makes
the actual planar exponent equal to the local sorted-direction exponent.

No delta < 1/2, fractional-width specialization, or globally chosen
Boolean recolouring is used. The only width assumption is 0<t<n+1.

Every loss word has two distinct adjacent active flip coordinates.
If neither flipped word is uncovered, the blockers must be distinct.
A global weighted Hall injection is still an open geometric step.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_projected_loss_two_disjoint_flip_exits_any_width
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
    (i : ProjectionOrdered V)
    (hloss :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let D := genericDirectionData_sendov hp hcap htpos hlam
      let B := standardResidualColoring D n
        (by exact_mod_cast htwidth)
      i ∈ projectedLossVertices B
        (fun j => centreExponent (cycles j) t)) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D n
      (by exact_mod_cast htwidth)
    ∃ c d : Fin n,
      c.val + 1 = d.val ∧
      c ∈ retainedActive B i ∧
      d ∈ retainedActive B i ∧
      ∀ word : Fin n → Bool,
        word ∈ retainedCompletionWords B i →
          Disjoint
            (completionFibre B (flipBoolWordAt word c))
            (completionFibre B (flipBoolWordAt word d)) ∧
          ((completionFibre B (flipBoolWordAt word c)).card = 0 ∨
           (completionFibre B (flipBoolWordAt word d)).card = 0 ∨
           ∃ w z : ProjectionOrdered V, w ≠ z ∧
             flipBoolWordAt word c ∈ retainedCompletionWords B w ∧
             flipBoolWordAt word d ∈ retainedCompletionWords B z) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast htwidth)
  let localCycles : ∀ j : ProjectionOrdered V, LocalDirectionCycle D j :=
    fun j => projectionCutLocalCycle hp hcap htpos hlam j (cycles j)
  have heq :
      ∀ j : ProjectionOrdered V,
        (localCycles j).exponent = centreExponent (cycles j) t := by
    intro j
    exact projectionCutLocalCycle_exponent_eq_centreExponent
      hp hcap htpos hlam j (cycles j)
  have hfunctions :
      (fun j => (localCycles j).exponent) =
        (fun j => centreExponent (cycles j) t) := by
    funext j
    exact heq j
  have hLoss' :
      i ∈ projectedLossVertices B
        (fun j => (localCycles j).exponent) := by
    rw [hfunctions]
    exact hloss
  exact projected_loss_two_disjoint_flip_exits
    D htwidth localCycles i hLoss'

#print axioms planar_projected_loss_two_disjoint_flip_exits_any_width

end ProjectionOrdered
end JSP000404Research
