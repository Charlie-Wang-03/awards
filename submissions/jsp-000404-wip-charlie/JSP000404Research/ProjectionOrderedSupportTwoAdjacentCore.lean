import JSP000404Research.FourSupportTwoOrderedAdjacent
import JSP000404Research.ResidualLossDirectionalWitness
import Mathlib.Tactic

/-!
# Abstract projected-loss ordered support-two terminal

This lightweight theorem contains the exact combinatorial/geometric core used
by the planar specialization:

* a<b<c<d;
* b is a projected-loss vertex for an arbitrary ordered residual colouring;
* the usual exponent upper bound and one-layer active-colour budget hold;
* the four-centre state is already reduced to the three double-transposition
  patterns.

Then all three edges incident to b are retained, opposite-side retained rays
cannot be delta-small, and only the ordered-adjacent pattern survives.

The concrete planar exponent/budget construction is intentionally kept out of
this module so the terminal can be kernel-checked independently of the older
projection-cut local-cycle infrastructure.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem projectedLoss_ordered_pattern3_reduce_to_adjacent_core
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn1 : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (R : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (hone : ∀ q, (active R q).card ≤ n - exponent q + 1)
    {a b c d : V}
    (hab : a < b)
    (hbc : b < c)
    (hcd : c < d)
    (hbLoss : b ∈ projectedLossVertices R exponent)
    (hpat :
      FourSupportTwoDerangementPattern3
        p delta lam a b c d)
    (hretainedAngle :
      ∀ {x i y : V},
        x < i →
        i < y →
        (R.color x i).val < n →
        (R.color i y).val < n →
        delta * lam <
          EuclideanGeometry.angle (p x) (p i) (p y)) :
    FourSupportTwoOrderedAdjacentPattern
      p delta lam a b c d := by
  have hretAB : (R.color a b).val < n :=
    projectedLoss_edge_left_retained
      R exponent hexp hone hbLoss hab
  have hretBC : (R.color b c).val < n :=
    projectedLoss_edge_right_retained
      R exponent hexp hone hbLoss hbc
  have hbd : b < d := hbc.trans hcd
  have hretBD : (R.color b d).val < n :=
    projectedLoss_edge_right_retained
      R exponent hexp hone hbLoss hbd

  have hbadABC :
      delta * lam <
        EuclideanGeometry.angle (p a) (p b) (p c) :=
    hretainedAngle hab hbc hretAB hretBC
  have hbadABD :
      delta * lam <
        EuclideanGeometry.angle (p a) (p b) (p d) :=
    hretainedAngle hab hbd hretAB hretBD

  exact four_supportTwo_pattern3_reduce_to_ordered_adjacent
    hpat hbadABD hbadABC

#print axioms projectedLoss_ordered_pattern3_reduce_to_adjacent_core

end ProjectionOrdered
end JSP000404Research
