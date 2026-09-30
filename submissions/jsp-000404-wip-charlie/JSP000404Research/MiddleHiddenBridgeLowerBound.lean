import JSP000404Research.SupportThreeMiddleHiddenSeparatedPattern
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-!
# Large cross angle forces a large hidden bridge

A middle-hidden support-three centre has the cyclic pattern

  top --large-- r --small-- b --bridge-- c --small-- d --large-- top,

with

  angle(r,i,b) + angle(c,i,d) <= delta*lambda.

If any cross-cluster angle between {r,b} and {c,d} has a lower bound L, then
the direct hidden bridge angle(b,i,c) has lower bound

  L - delta*lambda.

The statement uses only angular triangle inequalities and the retained
zero-angle budget.  In particular, a support-one residual lower bound

  ((n-2)-delta)*lambda

upgrades the hidden bridge to

  ((n-2)-2*delta)*lambda.

This isolates the exact geometric conversion needed before returning to
quotient arithmetic.
-/

namespace JSP000404Research

open Real

namespace MiddleHiddenSeparatedPatternAwayFromTop

theorem bridge_ge_cross_rc_sub_budget
    {V : Type*} {p : V → Plane}
    {top i : V} {delta lam L : ℝ}
    (M : MiddleHiddenSeparatedPatternAwayFromTop
      p top i delta lam)
    (hcross :
      L ≤ EuclideanGeometry.angle (p M.r.1) (p i) (p M.c.1)) :
    L - delta * lam ≤
      EuclideanGeometry.angle (p M.b.1) (p i) (p M.c.1) := by
  have hpath :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p i) (p M.r.1) (p M.b.1) (p M.c.1)
  have hsmall1 :
      EuclideanGeometry.angle (p M.r.1) (p i) (p M.b.1)
        ≤ delta * lam := by
    have hsmall2 :
        0 ≤ EuclideanGeometry.angle (p M.c.1) (p i) (p M.d.1) :=
      EuclideanGeometry.angle_nonneg _ _ _
    linarith [M.small_sum]
  linarith

theorem bridge_ge_cross_bd_sub_budget
    {V : Type*} {p : V → Plane}
    {top i : V} {delta lam L : ℝ}
    (M : MiddleHiddenSeparatedPatternAwayFromTop
      p top i delta lam)
    (hcross :
      L ≤ EuclideanGeometry.angle (p M.b.1) (p i) (p M.d.1)) :
    L - delta * lam ≤
      EuclideanGeometry.angle (p M.b.1) (p i) (p M.c.1) := by
  have hpath :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p i) (p M.b.1) (p M.c.1) (p M.d.1)
  have hsmall2 :
      EuclideanGeometry.angle (p M.c.1) (p i) (p M.d.1)
        ≤ delta * lam := by
    have hsmall1 :
        0 ≤ EuclideanGeometry.angle (p M.r.1) (p i) (p M.b.1) :=
      EuclideanGeometry.angle_nonneg _ _ _
    linarith [M.small_sum]
  linarith

theorem bridge_ge_cross_rd_sub_budget
    {V : Type*} {p : V → Plane}
    {top i : V} {delta lam L : ℝ}
    (M : MiddleHiddenSeparatedPatternAwayFromTop
      p top i delta lam)
    (hcross :
      L ≤ EuclideanGeometry.angle (p M.r.1) (p i) (p M.d.1)) :
    L - delta * lam ≤
      EuclideanGeometry.angle (p M.b.1) (p i) (p M.c.1) := by
  have hpath1 :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p i) (p M.r.1) (p M.b.1) (p M.d.1)
  have hpath2 :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p i) (p M.b.1) (p M.c.1) (p M.d.1)
  linarith [M.small_sum]

/-- Uniform specialization to the support-one lower bound. -/
theorem bridge_ge_supportOne_threshold_of_cross
    {V : Type*} {p : V → Plane}
    {top i : V} {delta lam : ℝ} {n : ℕ}
    (M : MiddleHiddenSeparatedPatternAwayFromTop
      p top i delta lam)
    (hcross :
      (((n - 2 : ℕ) : ℝ) - delta) * lam ≤
          EuclideanGeometry.angle (p M.r.1) (p i) (p M.c.1)
      ∨
      (((n - 2 : ℕ) : ℝ) - delta) * lam ≤
          EuclideanGeometry.angle (p M.b.1) (p i) (p M.d.1)
      ∨
      (((n - 2 : ℕ) : ℝ) - delta) * lam ≤
          EuclideanGeometry.angle (p M.r.1) (p i) (p M.d.1)
      ∨
      (((n - 2 : ℕ) : ℝ) - delta) * lam ≤
          EuclideanGeometry.angle (p M.b.1) (p i) (p M.c.1)) :
    (((n - 2 : ℕ) : ℝ) - 2 * delta) * lam ≤
      EuclideanGeometry.angle (p M.b.1) (p i) (p M.c.1) := by
  rcases hcross with hrc | hbd | hrd | hbc
  · have h :=
      M.bridge_ge_cross_rc_sub_budget hrc
    ring_nf at h ⊢
    linarith
  · have h :=
      M.bridge_ge_cross_bd_sub_budget hbd
    ring_nf at h ⊢
    linarith
  · have h :=
      M.bridge_ge_cross_rd_sub_budget hrd
    ring_nf at h ⊢
    linarith
  · ring_nf at hbc ⊢
    linarith

#print axioms MiddleHiddenSeparatedPatternAwayFromTop.bridge_ge_cross_rc_sub_budget
#print axioms MiddleHiddenSeparatedPatternAwayFromTop.bridge_ge_cross_bd_sub_budget
#print axioms MiddleHiddenSeparatedPatternAwayFromTop.bridge_ge_cross_rd_sub_budget
#print axioms MiddleHiddenSeparatedPatternAwayFromTop.bridge_ge_supportOne_threshold_of_cross

end MiddleHiddenSeparatedPatternAwayFromTop
end JSP000404Research
