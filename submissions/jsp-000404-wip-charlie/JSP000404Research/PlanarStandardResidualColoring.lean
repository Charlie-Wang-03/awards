import JSP000404Research.GenericForwardAngleLift
import JSP000404Research.StandardResidual
import Mathlib.Tactic

/-!
# Lightweight planar standard residual colouring

The standard lower-branch residual colouring is a small construction and is
used by many local geometric arguments.  It is kept separate from the much
heavier residual-capacity / hard-remainder assembly so those local arguments
do not inherit unrelated dependencies.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

noncomputable def planarStandardResidualColoring
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    OrderedEdgeColoring (ProjectionOrdered V) (n + 1) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (1 : ℝ) ≤ n := by
      exact_mod_cast hn
    linarith
  let D :=
    genericDirectionData_sendov hp hcap htpos hlam
  have hwidth : t < (n + 1 : ℕ) := by
    rw [ht]
    exact_mod_cast
      (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
  exact standardResidualColoring D n hwidth

#print axioms planarStandardResidualColoring

end ProjectionOrdered
end JSP000404Research
