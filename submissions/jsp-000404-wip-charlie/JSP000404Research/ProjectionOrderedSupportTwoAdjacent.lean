import JSP000404Research.FourSupportTwoOrderedAdjacent
import JSP000404Research.ResidualLossDirectionalWitness
import JSP000404Research.PlanarCentreExponent
import Mathlib.Tactic

/-!
# Projected-loss specialization of the ordered adjacent terminal

A projected-loss centre has no incident residual edge.  Therefore, for an
ordered quadruple a<b<c<d, if the second vertex b is projected-loss, all three
edges from b to a,c,d are retained.

Combining this with the opposite-side retained-angle obstruction turns any
three-pattern support-two terminal on (a,b,c,d) into the unique adjacent
matching {a,b}|{c,d}.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem projectedLoss_ordered_pattern3_reduce_to_adjacent
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn1 : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {a b c d : ProjectionOrdered V}
    (hab :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      a < b)
    (hbc :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      b < c)
    (hcd :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      c < d)
    (hbLoss :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      b ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn1 hdelta0 hdelta1 ht hlam)
        (planarCentreExponent (t := t) hp Cfam))
    (hpat :
      FourSupportTwoDerangementPattern3
        (reindexedPoint p) delta lam a b c d) :
    FourSupportTwoOrderedAdjacentPattern
      (reindexedPoint p) delta lam a b c d := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent (t := t) hp Cfam

  have hexp : ∀ q, exponent q ≤ n := by
    exact planarCentreExponent_le_n_light
      hp hn1 hdelta0 hdelta1 ht Cfam
  have hone :
      ∀ q, (active R q).card ≤ n - exponent q + 1 := by
    intro q
    simpa [R, exponent, planarCentreExponent] using
      (planarStandardResidual_active_card_le_oneLayer
        hp hcap hn1 hdelta0 hdelta1 ht hlam q (Cfam q))

  have hretAB : (R.color a b).val < n :=
    projectedLoss_edge_left_retained
      R exponent hexp hone
      (by simpa [R, exponent] using hbLoss) hab
  have hretBC : (R.color b c).val < n :=
    projectedLoss_edge_right_retained
      R exponent hexp hone
      (by simpa [R, exponent] using hbLoss) hbc
  have hbd : b < d := hbc.trans hcd
  have hretBD : (R.color b d).val < n :=
    projectedLoss_edge_right_retained
      R exponent hexp hone
      (by simpa [R, exponent] using hbLoss) hbd

  exact retained_ordered_pattern3_reduce_to_adjacent
    hp hcap hn1 hdelta0 hdelta1 ht hlam
    hab hbc hcd
    (by simpa [R] using hretAB)
    (by simpa [R] using hretBC)
    (by simpa [R] using hretBD)
    hpat

#print axioms projectedLoss_ordered_pattern3_reduce_to_adjacent

end ProjectionOrdered
end JSP000404Research
