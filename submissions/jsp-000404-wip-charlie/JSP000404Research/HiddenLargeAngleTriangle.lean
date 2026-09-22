import JSP000404Research.GeneralNontransitionPayment
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-!
# Skinny triangle forced by the hidden n-1 angle

Under Sendov normalization

  t = n + delta,
  lambda = pi/t,

a genuine angle of size at least (n-1)*lambda leaves at most

  (1+delta)*lambda

for the other two angles of its triangle.

In the lower branch delta<1/2, their total is strictly below 3/2 lambda.

Combined with GeneralNontransitionPayment, every support-two deficit-two centre
whose transition quotient is one therefore determines a very skinny triangle:
the hidden adjacent-ray angle is large and the two endpoint angles have a
small total.
-/

namespace JSP000404Research

open Real

theorem triangle_other_angles_sum_le_one_add_delta_lam
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t lam delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (htpos : 0 < t)
    {i x y : V}
    (hix : i ≠ x)
    (hiy : i ≠ y)
    (hxy : x ≠ y)
    (hlarge :
      (((n - 1 : ℕ) : ℝ) * lam) ≤
        EuclideanGeometry.angle (p x) (p i) (p y)) :
    EuclideanGeometry.angle (p i) (p x) (p y) +
        EuclideanGeometry.angle (p i) (p y) (p x)
      ≤ (1 + delta) * lam := by
  have hpi : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  have hsum :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p x) (p₂ := p i) (p y)
      (hp.ne hix.symm)
  have hcommY :
      EuclideanGeometry.angle (p y) (p x) (p i) =
        EuclideanGeometry.angle (p i) (p x) (p y) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcommY] at hsum
  have hncast :
      (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    exact_mod_cast (Nat.sub_add_cancel hn)
  rw [hncast, hpi, ht] at hsum hlarge
  nlinarith

theorem triangle_other_angles_sum_lt_three_halves_lam
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t lam delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (htpos : 0 < t)
    {i x y : V}
    (hix : i ≠ x)
    (hiy : i ≠ y)
    (hxy : x ≠ y)
    (hlarge :
      (((n - 1 : ℕ) : ℝ) * lam) ≤
        EuclideanGeometry.angle (p x) (p i) (p y)) :
    EuclideanGeometry.angle (p i) (p x) (p y) +
        EuclideanGeometry.angle (p i) (p y) (p x)
      < (3 : ℝ) / 2 * lam := by
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have h :=
    triangle_other_angles_sum_le_one_add_delta_lam
      hp hn ht hlam htpos
      hix hiy hxy hlarge
  nlinarith

/-- Concrete support-two / unit-transition specialization. -/
theorem support_two_unit_transition_skinny_triangle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (pre post : List ℕ)
    (qe : ℕ)
    (hrays : C.rays = first :: rest)
    (hqe0 : qe ≠ 0)
    (hq :
      quotientList t C.gaps =
        pre ++ qe :: post)
    (hsignLift :
      liftedCentreSignPath hp i first rest =
        List.replicate pre.length (raySignAt hp i first) ++
          List.replicate (post.length + 1)
            (!raySignAt hp i first))
    (hqeOne : qe = 1) :
    ∃ x y : OtherVertex i,
      x ≠ y ∧
      (((n - 1 : ℕ) : ℝ) * lam) ≤
        EuclideanGeometry.angle (p x.1) (p i) (p y.1) ∧
      EuclideanGeometry.angle (p i) (p x.1) (p y.1) +
          EuclideanGeometry.angle (p i) (p y.1) (p x.1)
        < (3 : ℝ) / 2 * lam := by
  obtain ⟨x, y, hxy, hlarge⟩ :=
    support_two_unit_transition_hidden_angle
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      i C hexp hsupport
      first rest pre post qe
      hrays hqe0 hq hsignLift hqeOne
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hskinny :=
    triangle_other_angles_sum_lt_three_halves_lam
      hp (by omega : 1 ≤ n)
      hdeltaHalf ht hlam htpos
      x.2.symm y.2.symm
      (by
        intro h
        apply hxy
        exact Subtype.ext h)
      hlarge
  exact ⟨x, y, hxy, hlarge, hskinny⟩

#print axioms triangle_other_angles_sum_le_one_add_delta_lam
#print axioms triangle_other_angles_sum_lt_three_halves_lam
#print axioms support_two_unit_transition_skinny_triangle

end JSP000404Research
