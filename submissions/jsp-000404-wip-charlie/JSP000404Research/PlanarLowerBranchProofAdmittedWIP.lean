import JSP000404Research.PlanarLowerBranchFullProofInterface
import Mathlib.Tactic

/-!
# ADMITTED RESEARCH-ONLY ENTRY: lower-branch dyadic capacity

Exactly TWO deliberately unresolved geometric obligations are provisionally
admitted below.  Neither is a theorem: both are Lean sorry placeholders.

Gap 1: every inclusion-minimal enlarged Hall deficient core contains a
genuine projected-loss centre (exclusion of non-loss-only cores).

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
  exact planar_lower_branch_dyadic_capacity_of_geometric_gaps
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
    (by
      -- OPEN GEOMETRY GAP G1: minimal deficient core has a loss vertex.
      sorry)
    (by
      -- OPEN GEOMETRY GAP G2: strict geometric collision-mass exclusion.
      sorry)

#print axioms planar_lower_branch_dyadic_capacity_admitted_wip

end ProjectionOrdered
end JSP000404Research
