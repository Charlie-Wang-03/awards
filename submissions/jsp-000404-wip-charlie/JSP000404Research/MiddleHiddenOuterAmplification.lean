import JSP000404Research.SupportThreeMiddleHiddenSeparatedPattern
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-!
# A large angle to one residual vertex strengthens an outer middle-hidden edge

For a six-point middle-hidden pattern at centre i, the four non-top vertices
are exactly r,b,c,d and

  angle(r,i,b) + angle(c,i,d) <= delta*lambda.

If one non-top/non-centre vertex a satisfies

  L <= angle(top,i,a),

then at least one of the two outer transition edges satisfies

  L - delta*lambda <= angle(top,i,r)

or

  L - delta*lambda <= angle(d,i,top).

This is independent of the quotient arithmetic and uses only the angular
triangle inequality plus the retained zero-angle budget.
-/

namespace JSP000404Research

open Real

namespace MiddleHiddenSeparatedPatternAwayFromTop

theorem outer_large_of_large_to_other_vertex
    {V : Type*} [Fintype V] [DecidableEq V]
    {p : V → Plane}
    {top i a : V} {delta lam L : ℝ}
    (M : MiddleHiddenSeparatedPatternAwayFromTop
      p top i delta lam)
    (hcard : Fintype.card V = 6)
    (hit : i ≠ top)
    (haTop : a ≠ top)
    (haI : a ≠ i)
    (hdelta0 : 0 ≤ delta)
    (hlampos : 0 < lam)
    (hlarge :
      L ≤ EuclideanGeometry.angle (p top) (p i) (p a)) :
    L - delta * lam ≤
        EuclideanGeometry.angle (p top) (p i) (p M.r.1)
      ∨
    L - delta * lam ≤
        EuclideanGeometry.angle (p M.d.1) (p i) (p top) := by
  have hsmall1 :
      EuclideanGeometry.angle (p M.r.1) (p i) (p M.b.1)
        ≤ delta * lam := by
    have hnonneg :
        0 ≤ EuclideanGeometry.angle (p M.c.1) (p i) (p M.d.1) :=
      EuclideanGeometry.angle_nonneg _ _ _
    linarith [M.small_sum]
  have hsmall2 :
      EuclideanGeometry.angle (p M.c.1) (p i) (p M.d.1)
        ≤ delta * lam := by
    have hnonneg :
        0 ≤ EuclideanGeometry.angle (p M.r.1) (p i) (p M.b.1) :=
      EuclideanGeometry.angle_nonneg _ _ _
    linarith [M.small_sum]
  rcases M.covers_every_other_nonTop hcard hit haTop haI with
    har | hab | hac | had
  · left
    subst a
    nlinarith
  · left
    subst a
    have hpath :=
      EuclideanGeometry.angle_le_angle_add_angle
        (p i) (p top) (p M.r.1) (p M.b.1)
    nlinarith
  · right
    subst a
    have hpath :=
      EuclideanGeometry.angle_le_angle_add_angle
        (p i) (p top) (p M.d.1) (p M.c.1)
    have hcommOuter :
        EuclideanGeometry.angle (p top) (p i) (p M.d.1) =
          EuclideanGeometry.angle (p M.d.1) (p i) (p top) :=
      EuclideanGeometry.angle_comm _ _ _
    have hcommSmall :
        EuclideanGeometry.angle (p M.d.1) (p i) (p M.c.1) =
          EuclideanGeometry.angle (p M.c.1) (p i) (p M.d.1) :=
      EuclideanGeometry.angle_comm _ _ _
    rw [hcommOuter, hcommSmall] at hpath
    nlinarith
  · right
    subst a
    have hcomm :
        EuclideanGeometry.angle (p top) (p i) (p M.d.1) =
          EuclideanGeometry.angle (p M.d.1) (p i) (p top) :=
      EuclideanGeometry.angle_comm _ _ _
    rw [hcomm] at hlarge
    nlinarith

#print axioms MiddleHiddenSeparatedPatternAwayFromTop.outer_large_of_large_to_other_vertex

end MiddleHiddenSeparatedPatternAwayFromTop
end JSP000404Research
