import JSP000404Research.FourCentreMixedTransitionWitness
import JSP000404Research.ThreeRayNontransitionPayment
import JSP000404Research.FinFourOtherPairs
import JSP000404Research.TriangleConvexCone
import Mathlib.Tactic

/-!
# The mixed interior support-two centre has an almost-hidden large angle

In the mixed pattern, let a be the support-one deficit-two centre and b the
support-two deficit-two centre.  The preserved transition witness at b has
transition quotient exactly 1.  Deficit-two arithmetic then supplies the other
positive quotient n-1.

Because n-1 != 1, ThreeRayNontransitionPayment turns that hidden quotient into
a genuine angle of size at least (n-1)*lambda between two of the three rays
{s,a,c} at b.

SharpOuterAngles plus the unique zero quotient already imply

  angle(a,b,c) <= delta*lambda.

Hence the hidden large pair cannot be {a,c}.  If it is {s,c}, we immediately
obtain the desired lower bound.  If it is {s,a}, convex-hull angle splitting
subtracts at most delta*lambda.  In both cases

  ((n-1)-delta)*lambda <= angle(s,b,c).

This is exactly the weakened hidden-angle input required by the short interior
arithmetic contradiction.
-/

namespace JSP000404Research

open Real

theorem mixed_inside_hidden_angle_weakened_fin_four
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
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) = 2)
    (hinside :
      p c ∈ convexHull ℝ
        ({p s, p a, p b} : Set Plane)) :
    (((n - 1 : ℕ) : ℝ) - delta) * lam ≤
      EuclideanGeometry.angle (p s) (p b) (p c) := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hsSharp :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hlam
      s Cs hS
  obtain ⟨xb, yb, hxyb, hsmallB⟩ :=
    exists_small_angle_pair_of_four_centre_deficit_two_support_two
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      b Cb hB hsupB
  have hpairB :
      (xb.1 = a ∧ yb.1 = c) ∨
        (xb.1 = c ∧ yb.1 = a) := by
    exact small_pair_at_outer_eq_other_outer_pair
      hp hcap hdeltaHalf hlampos
      hsb hsa hsc hab.symm hbc hac
      hsSharp xb yb hxyb hsmallB
  have hsmallAC :
      EuclideanGeometry.angle (p a) (p b) (p c) ≤
        delta * lam := by
    rcases hpairB with h | h
    · simpa [h.1, h.2] using hsmallB
    · have h' := hsmallB
      rw [h.1, h.2] at h'
      simpa only [EuclideanGeometry.angle_comm] using h'
  obtain ⟨first, rest, pre, post, qe,
      hrays, hqe, hq, hsignLift⟩ :=
    concrete_centre_large_exponent_has_positive_transition_gap
      hp hcap (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht hlam
      b Cb (by rw [hB]; omega)
  have hqeOne :
      qe = 1 :=
    mixed_transition_decomposition_qe_eq_one
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hab
      Cs Ca Cb hS hA hsupA
      first rest pre post qe
      hrays hqe hq hsignLift
  obtain ⟨HB, hHBeq⟩ :=
    exists_highExponentTransitionIntervalCertificate_of_decomposition
      hp htpos b Cb first rest pre post qe
      hrays hqe hq hsignLift
  have hHBOne : HB.qe = 1 := by
    rw [hHBeq, hqeOne]
  have hhidden :
      n - 1 ∈ quotientList t Cb.gaps :=
    mixed_support_two_has_hidden_n_sub_one
      Cb HB hn hdelta0 hdeltaHalf ht
      hB hsupB hHBOne
  have hlen := centreProjectiveCycle_rays_length_fin4 b Cb
  rw [hrays] at hlen
  have hrestLen : rest.length = 2 := by
    simpa using hlen
  obtain ⟨r1, r2, hrest⟩ := List.length_eq_two.mp hrestLen
  subst rest
  have hqne : n - 1 ≠ qe := by
    rw [hqeOne]
    omega
  obtain ⟨x, y, hxy, hlarge⟩ :=
    exists_actual_angle_paying_nontransition_quotient_fin_four
      hp htpos hlam b Cb first r1 r2
      (by simpa using hrays)
      pre post qe (n - 1)
      hq
      (by simpa using hsignLift)
      hqne hhidden
  have hcases :=
    other_pair_at_b_three_cases_fin_four
      hsa hsb hsc hab hac hbc
      x y hxy
  have hnsubR :
      (2 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 ≤ n - 1)
  rcases hcases with hSA | hSC | hAC
  · have hlargeSA :
        ((n - 1 : ℕ) : ℝ) * lam ≤
          EuclideanGeometry.angle (p s) (p b) (p a) := by
      rcases hSA with h | h
      · simpa [h.1, h.2] using hlarge
      · have h' := hlarge
        rw [h.1, h.2] at h'
        simpa only [EuclideanGeometry.angle_comm] using h'
    have hsplitB :
        EuclideanGeometry.angle (p s) (p b) (p a) =
          EuclideanGeometry.angle (p s) (p b) (p c) +
            EuclideanGeometry.angle (p c) (p b) (p a) := by
      exact angle_split_at_third_of_mem_convexHull_three
        hinside (hp.ne hbc.symm)
    have hsmallCA :
        EuclideanGeometry.angle (p c) (p b) (p a) ≤
          delta * lam := by
      rw [EuclideanGeometry.angle_comm]
      exact hsmallAC
    nlinarith
  · have hlargeSC :
        ((n - 1 : ℕ) : ℝ) * lam ≤
          EuclideanGeometry.angle (p s) (p b) (p c) := by
      rcases hSC with h | h
      · simpa [h.1, h.2] using hlarge
      · have h' := hlarge
        rw [h.1, h.2] at h'
        simpa only [EuclideanGeometry.angle_comm] using h'
    nlinarith
  · have hlargeAC :
        ((n - 1 : ℕ) : ℝ) * lam ≤
          EuclideanGeometry.angle (p a) (p b) (p c) := by
      rcases hAC with h | h
      · simpa [h.1, h.2] using hlarge
      · have h' := hlarge
        rw [h.1, h.2] at h'
        simpa only [EuclideanGeometry.angle_comm] using h'
    exfalso
    nlinarith

#print axioms mixed_inside_hidden_angle_weakened_fin_four

end JSP000404Research
