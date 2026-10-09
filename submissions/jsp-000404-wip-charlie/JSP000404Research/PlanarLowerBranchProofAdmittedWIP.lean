import JSP000404Research.PlanarLowerBranchInternalResidualExactBoundaryInterface
-- Incremental CI sentinel: this WIP theorem still has two explicit geometric sorry gaps.
import Mathlib.Tactic

/-!
# ADMITTED RESEARCH-ONLY ENTRY: lower-branch dyadic capacity

Exactly TWO deliberately unresolved geometric obligations are provisionally
admitted below.  Neither is a theorem: both are Lean sorry placeholders.

Gap 1 (REFINED, **ABSTRACTLY REFUTED**): exclude EXACT non-loss
vertices (k=projectedFree) with a core-internal residual-edge neighbour
in loss-free minimal Hall-deficient cores. An explicit 3-point genuine
DirectionData example shows the unrestricted G1 predicate is FALSE:
see DirectionDataThreePointG1HallRefutation.lean (verified in incremental
CI run 37925153278). Thus the first sorry CANNOT be discharged using
DirectionData axioms alone; a stronger planar-specific mechanism or a
replacement capacity strategy is necessary. No planar realizability
conclusion is made by that finite abstract counterexample.

Gap 2: true planar cyclic/triangle geometry supplies a strict upper
bound on shared words at a minimal deficient projected-loss centre,
contradicting the verified |Q_v|+Delta(T) lower bound.

All other derivations are imported from already kernel-checked modules.
This WIP theorem's #print axioms MUST contain sorryAx until both geometry
lemmas are proved.  Do NOT submit or describe it as a proof of JSP-000404.
This covers only the Sendov-normalized LOWER BRANCH, not the full problem.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- PROVISIONAL. Complete theorem-shaped lower-branch Lean assembly
with only two openly admitted geometric obligations. -/
theorem planar_lower_branch_dyadic_capacity_admitted_wip
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (cycles i) t) ≤ 2 ^ n := by
  exact planar_lower_branch_dyadic_capacity_of_internal_residual_exact_boundary
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
    (by
      -- UNSOLVED planar G1-INTERNAL. The corresponding universal
      -- DirectionData exclusion is formally FALSE (3-point counterexample).
      -- Do not fill this hole by assuming the abstract predicate.
      sorry)
    (by
      -- OPEN GEOMETRY GAP G2: strict global collision-mass exclusion.
      sorry)

#print axioms planar_lower_branch_dyadic_capacity_admitted_wip

end ProjectionOrdered
end JSP000404Research
