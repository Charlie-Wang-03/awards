import JSP000404Research.FourSupportTwoDerangement
import JSP000404Research.ProjectionOppositeSideRetainedAngle
import Mathlib.Tactic

/-!
# Ordered all-support-two terminal: only the adjacent matching survives

For a<b<c<d, the three double-transposition patterns have a simple order
interpretation.  At the second vertex b:

* pattern 1 asks the opposite-side pair {a,d} to be delta-small;
* pattern 2 asks the opposite-side pair {a,c} to be delta-small;
* pattern 3 asks the same-side pair {c,d} to be delta-small.

Thus once the three incident edges at b are retained, the general
opposite-side retained-angle obstruction eliminates the first two patterns.
The surviving pattern is the adjacent matching {a,b}|{c,d}.
-/

namespace JSP000404Research

def FourSupportTwoOrderedAdjacentPattern
    {V : Type*}
    (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam ∧
  EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam ∧
  EuclideanGeometry.angle (p a) (p c) (p b) ≤ delta * lam ∧
  EuclideanGeometry.angle (p a) (p d) (p b) ≤ delta * lam

theorem four_supportTwo_pattern3_reduce_to_ordered_adjacent
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    {a b c d : V}
    (hpat : FourSupportTwoDerangementPattern3 p delta lam a b c d)
    (hbadABD :
      delta * lam <
        EuclideanGeometry.angle (p a) (p b) (p d))
    (hbadABC :
      delta * lam <
        EuclideanGeometry.angle (p a) (p b) (p c)) :
    FourSupportTwoOrderedAdjacentPattern p delta lam a b c d := by
  unfold FourSupportTwoDerangementPattern3 at hpat
  unfold FourSupportTwoAnglePattern3Core at hpat
  unfold FourSupportTwoOrderedAdjacentPattern
  rcases hpat with h1 | h2 | h3
  · exfalso
    linarith [h1.2.1]
  · exfalso
    linarith [h2.2.1]
  · exact h3

namespace ProjectionOrdered

open OrderedEdgeColoring

theorem retained_ordered_pattern3_reduce_to_adjacent
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
    (hretAB :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn1 hdelta0 hdelta1 ht hlam
      (R.color a b).val < n)
    (hretBC :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn1 hdelta0 hdelta1 ht hlam
      (R.color b c).val < n)
    (hretBD :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn1 hdelta0 hdelta1 ht hlam
      (R.color b d).val < n)
    (hpat :
      FourSupportTwoDerangementPattern3
        (reindexedPoint p) delta lam a b c d) :
    FourSupportTwoOrderedAdjacentPattern
      (reindexedPoint p) delta lam a b c d := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hac : a < c := hab.trans hbc
  have hbd : b < d := hbc.trans hcd
  have hbadABD :=
    opposite_side_retained_angle_gt_delta
      hp hcap hn1 hdelta0 hdelta1 ht hlam
      hab hbd hretAB hretBD
  have hbadABC :=
    opposite_side_retained_angle_gt_delta
      hp hcap hn1 hdelta0 hdelta1 ht hlam
      hab hbc hretAB hretBC
  exact four_supportTwo_pattern3_reduce_to_ordered_adjacent
    hpat hbadABD hbadABC

#print axioms four_supportTwo_pattern3_reduce_to_ordered_adjacent
#print axioms retained_ordered_pattern3_reduce_to_adjacent

end ProjectionOrdered
end JSP000404Research
