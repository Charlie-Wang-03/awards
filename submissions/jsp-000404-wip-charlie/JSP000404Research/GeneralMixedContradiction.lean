import JSP000404Research.GeneralMixedExteriorContradiction
import JSP000404Research.GeneralMixedInteriorContradiction
import JSP000404Research.SharpSupportTwoLargeAngle
import JSP000404Research.TransitionCertificateFromDecomposition
import Mathlib.Tactic

/-!
# Complete cardinality-free mixed contradiction with one fourth point

Fix distinct s,a,b,c in an arbitrary finite configuration.  Suppose

* s has exponent n-1;
* a has exponent n-2 and quotient support one;
* b has exponent n-2 and quotient support two.

The support-two transition quotient is forced to one by the transition-arc
packing of s,a,b.

If c lies outside conv{s,a,b}, GeneralMixedExteriorContradiction closes the
branch by restricting all support certificates to the four-point
subconfiguration.

If c lies inside the triangle, the unit transition at b plus the sharp centre
s gives the lower bound

  ((n-1)-delta)*lambda <= angle(s,b,c),

and GeneralMixedInteriorContradiction closes the branch.

Hence a top centre cannot coexist with one support-one and one support-two
deficit-two companion as soon as any fourth distinct point exists.
-/

namespace JSP000404Research

theorem no_top_mixed_deficitTwo_with_fourth
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
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1)
    (hsupB :
      positiveSupport (centreQuotient Cb t) = 2) :
    False := by
  by_cases hinside :
      p c ∈ convexHull ℝ
        ({p s, p a, p b} : Set Plane)
  · have hdelta1 : delta < 1 := by linarith
    have htpos :
        0 < t :=
      sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
    have hs :
        SharpAt p delta lam s :=
      concrete_unit_deficit_is_sharp
        hp hcap (by omega : 2 ≤ n)
        hdelta0 hdelta1 ht hlam
        s Cs hS

    obtain ⟨first, rest, pre, post, qe,
        hrays, hqe, hq, hsignLift⟩ :=
      concrete_centre_large_exponent_has_positive_transition_gap
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        b Cb (by rw [hB]; omega)

    let HS :=
      Classical.choice
        (exists_highExponentTransitionIntervalCertificate
          hp hcap (by omega : 1 ≤ n)
          hdelta0 hdelta1 ht hlam
          s Cs (by rw [hS]; omega))
    let HA :=
      Classical.choice
        (exists_highExponentTransitionIntervalCertificate
          hp hcap (by omega : 1 ≤ n)
          hdelta0 hdelta1 ht hlam
          a Ca (by rw [hA]; omega))
    obtain ⟨HB, hHB⟩ :=
      exists_highExponentTransitionIntervalCertificate_of_decomposition
        hp htpos b Cb first rest pre post qe
        hrays hqe hq hsignLift
    have hqeOneHB :
        HB.qe = 1 :=
      mixed_deficit_two_transition_qe_eq_one
        hp hn hdelta0 hdeltaHalf ht
        hsa hsb hab
        Cs Ca Cb HS HA HB
        hS hA hsupA
    have hqeOne : qe = 1 := by
      rw [hHB] at hqeOneHB
      exact hqeOneHB

    have hhidden :
        (((n - 1 : ℕ) : ℝ) - delta) * lam ≤
          EuclideanGeometry.angle (p s) (p b) (p c) :=
      sharp_supportTwo_unit_transition_angle_lower
        hp hcap hn hdelta0 hdeltaHalf ht hlam
        hsb hbc hsc.symm
        hs Cb hB hsupB
        first rest pre post qe
        hrays hqe hq hsignLift hqeOne

    exact no_mixed_fourth_inside_of_weakened_hidden_angle
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      hinside hhidden
  · exact no_mixed_fourth_outside_triangle
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      Cs Ca Cb hS hA hB hsupA hsupB hinside

#print axioms no_top_mixed_deficitTwo_with_fourth

end JSP000404Research
