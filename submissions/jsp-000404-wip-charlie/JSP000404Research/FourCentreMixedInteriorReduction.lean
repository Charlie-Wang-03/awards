import JSP000404Research.TriangleConvexCone
import JSP000404Research.FourCentreMixedInteriorShort
import JSP000404Research.SharpCentre
import Mathlib.Tactic

/-!
# Mixed interior branch reduced to one hidden-angle lower bound

Suppose c lies in the convex hull of the outer triangle s-a-b.  Convex-hull
cone geometry splits each outer angle through the ray to c.

The global angle cap applied to triangles s-a-c and a-b-c gives

  lambda <= angle(a,s,c) + angle(s,a,c),
  lambda <= angle(a,b,c) + angle(c,a,b).

Therefore the mixed interior branch is impossible as soon as the hidden
support-two quotient n-1 is known to be carried by angle(s,b,c).

This file packages all other geometry and arithmetic, leaving exactly that
quotient-to-angle identification as the remaining local statement.
-/

namespace JSP000404Research

open Real

theorem no_mixed_fourth_inside_of_hidden_angle_fin_four
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c : Fin 4}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hinside :
      p c ∈ convexHull ℝ
        ({p s, p a, p b} : Set Plane))
    (hhidden :
      ((n - 1 : ℕ) : ℝ) * lam ≤
        EuclideanGeometry.angle (p s) (p b) (p c)) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hpi : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  let As : ℝ :=
    EuclideanGeometry.angle (p a) (p s) (p b)
  let Aa : ℝ :=
    EuclideanGeometry.angle (p s) (p a) (p b)
  let Ab : ℝ :=
    EuclideanGeometry.angle (p s) (p b) (p a)
  let p0 : ℝ :=
    EuclideanGeometry.angle (p a) (p s) (p c)
  let u : ℝ :=
    EuclideanGeometry.angle (p s) (p a) (p c)
  let v : ℝ :=
    EuclideanGeometry.angle (p c) (p a) (p b)
  let w : ℝ :=
    EuclideanGeometry.angle (p s) (p b) (p c)
  let z : ℝ :=
    EuclideanGeometry.angle (p c) (p b) (p a)
  have hsplitS :
      As =
        p0 +
          EuclideanGeometry.angle (p c) (p s) (p b) := by
    dsimp [As, p0]
    exact angle_split_of_mem_convexHull_three
      hinside (hp.ne hsc.symm)
  have hp0 : p0 ≤ As := by
    have hnonneg :
        0 ≤ EuclideanGeometry.angle (p c) (p s) (p b) :=
      EuclideanGeometry.angle_nonneg _ _ _
    linarith
  have hsplitA :
      Aa = u + v := by
    dsimp [Aa, u, v]
    exact angle_split_at_second_of_mem_convexHull_three
      hinside (hp.ne hac.symm)
  have hsplitB :
      Ab = w + z := by
    dsimp [Ab, w, z]
    exact angle_split_at_third_of_mem_convexHull_three
      hinside (hp.ne hbc.symm)
  have houter :
      As + Aa + Ab = Real.pi := by
    have hsum :=
      EuclideanGeometry.angle_add_angle_add_angle_eq_pi
        (p₁ := p a) (p₂ := p s) (p b)
        (hp.ne hsa.symm)
    dsimp [As, Aa, Ab]
    have hcomm :
        EuclideanGeometry.angle (p b) (p a) (p s) =
          EuclideanGeometry.angle (p s) (p a) (p b) :=
      EuclideanGeometry.angle_comm _ _ _
    rw [hcomm] at hsum
    linarith
  have hpu : lam ≤ p0 + u := by
    have hsum :=
      EuclideanGeometry.angle_add_angle_add_angle_eq_pi
        (p₁ := p a) (p₂ := p s) (p c)
        (hp.ne hsa.symm)
    have hcapC :
        EuclideanGeometry.angle (p s) (p c) (p a) ≤
          Real.pi - lam :=
      hcap s c a hsc hsa hac.symm
    have hcomm :
        EuclideanGeometry.angle (p c) (p a) (p s) =
          EuclideanGeometry.angle (p s) (p a) (p c) :=
      EuclideanGeometry.angle_comm _ _ _
    rw [hcomm] at hsum
    dsimp [p0, u]
    linarith
  have hzv : lam ≤ z + v := by
    have hsum :=
      EuclideanGeometry.angle_add_angle_add_angle_eq_pi
        (p₁ := p a) (p₂ := p b) (p c)
        (hp.ne hab)
    have hcapC :
        EuclideanGeometry.angle (p b) (p c) (p a) ≤
          Real.pi - lam :=
      hcap b c a hbc hab.symm hac.symm
    dsimp [z, v]
    linarith
  exact mixed_four_interior_short_arithmetic_contradiction
    (by omega : 1 ≤ n)
    hlampos hdelta1 ht hpi houter
    hp0 hsplitA.le hsplitB.le
    (by simpa [w] using hhidden)
    hpu hzv

#print axioms no_mixed_fourth_inside_of_hidden_angle_fin_four

end JSP000404Research
