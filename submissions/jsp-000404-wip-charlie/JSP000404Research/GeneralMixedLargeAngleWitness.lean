import JSP000404Research.GeneralMixedTransitionWitness
import JSP000404Research.GeneralNontransitionPayment
import Mathlib.Tactic

/-!
# Genuine large-angle witness forced by the mixed three-centre pattern

In a finite planar AngleCap configuration, a sharp centre s, a deficit-two
support-one centre a, and a deficit-two support-two centre b force the
actual transition quotient at b to equal one.

The other positive quotient is then n-1, occurs on a same-sign step,
and pays a real Euclidean angle at b of at least (n-1)*lambda.

The selected endpoints x,y are actual distinct vertices, but are NOT
yet proved to have any prescribed identity among s, a, or remaining
vertices. Endpoint localization, not quotient value extraction, is the
next geometric obstacle.
-/

namespace JSP000404Research

theorem general_mixed_actual_large_angle_exists
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) = 2) :
    ∃ x y : OtherVertex b,
      x ≠ y ∧
      (((n - 1 : ℕ) : ℝ) * lam) ≤
        EuclideanGeometry.angle (p x.1) (p b) (p y.1) := by
  have hdelta1 : delta < 1 := by linarith
  obtain ⟨first, rest, pre, post, qe, hrays, hqe, hq, hsignLift⟩ :=
    concrete_centre_large_exponent_has_positive_transition_gap
      hp hcap (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht hlam
      b Cb (by rw [hB])
  have hqeOne : qe = 1 :=
    general_mixed_transition_decomposition_qe_eq_one
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hab Cs Ca Cb hS hA hsupA
      first rest pre post qe
      hrays hqe hq hsignLift
  exact support_two_unit_transition_hidden_angle
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    b Cb hB hsupB
    first rest pre post qe
    hrays hqe hq hsignLift hqeOne

#print axioms general_mixed_actual_large_angle_exists

end JSP000404Research
