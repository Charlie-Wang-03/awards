import JSP000404Research.SecondLayerFourSupportReduction
import JSP000404Research.HiddenLargeAngleTriangle
import JSP000404Research.TransitionCertificateFromDecomposition
import Mathlib.Tactic

/-!
# Skinny-triangle geometry in the exact-two support terminal

Suppose four distinct second-layer centres consist of two support-one and two
support-two centres.  Rebuild an explicit transition decomposition at each
support-two centre.  The two support-one transition quotients are n-1, while
both rebuilt support-two transition quotients are positive.  Four-centre
transition packing therefore forces both support-two transition quotients to
be exactly one.

Because the sign decompositions are retained, each support-two centre now
produces a genuine hidden (n-1)*lambda angle and hence a skinny triangle whose
other two angles have total < 3/2*lambda.
-/

namespace JSP000404Research

def SupportTwoSkinnyTriangle
    {V : Type*}
    (p : V → Plane) (lam : ℝ) (n : ℕ) (i : V) : Prop :=
  ∃ x y : V,
    x ≠ y ∧ x ≠ i ∧ y ≠ i ∧
    (((n - 1 : ℕ) : ℝ) * lam) ≤
      EuclideanGeometry.angle (p x) (p i) (p y) ∧
    EuclideanGeometry.angle (p i) (p x) (p y) +
        EuclideanGeometry.angle (p i) (p y) (p x)
      < (3 : ℝ) / 2 * lam

theorem twoSupportOne_twoSupportTwo_force_two_skinny_triangles
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {o₁ o₂ s₁ s₂ : V}
    (ho12 : o₁ ≠ o₂)
    (ho1s1 : o₁ ≠ s₁) (ho1s2 : o₁ ≠ s₂)
    (ho2s1 : o₂ ≠ s₁) (ho2s2 : o₂ ≠ s₂)
    (hs12 : s₁ ≠ s₂)
    (Co₁ : CentreProjectiveCycle hp o₁)
    (Co₂ : CentreProjectiveCycle hp o₂)
    (Cs₁ : CentreProjectiveCycle hp s₁)
    (Cs₂ : CentreProjectiveCycle hp s₂)
    (ho1Second : centreExponent Co₁ t = n - 2)
    (ho2Second : centreExponent Co₂ t = n - 2)
    (hs1Second : centreExponent Cs₁ t = n - 2)
    (hs2Second : centreExponent Cs₂ t = n - 2)
    (ho1Support :
      positiveSupport (centreQuotient Co₁ t) = 1)
    (ho2Support :
      positiveSupport (centreQuotient Co₂ t) = 1)
    (hs1Support :
      positiveSupport (centreQuotient Cs₁ t) = 2)
    (hs2Support :
      positiveSupport (centreQuotient Cs₂ t) = 2) :
    SupportTwoSkinnyTriangle p lam n s₁ ∧
    SupportTwoSkinnyTriangle p lam n s₂ := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :
      1 ≤ t :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht
  have hdelta1 : delta < 1 := by linarith

  obtain ⟨first₁,rest₁,pre₁,post₁,qe₁,
      hrays₁,hqe₁0,hq₁,hsign₁⟩ :=
    exists_transition_decomposition_of_support_le_two
      hp hcap htpos htone hlam
      s₁ Cs₁ (by rw [hs1Support]; omega)
  obtain ⟨H₁,hH₁qe⟩ :=
    exists_highExponentTransitionIntervalCertificate_of_decomposition
      hp htpos s₁ Cs₁ first₁ rest₁ pre₁ post₁ qe₁
      hrays₁ hqe₁0 hq₁ hsign₁

  obtain ⟨first₂,rest₂,pre₂,post₂,qe₂,
      hrays₂,hqe₂0,hq₂,hsign₂⟩ :=
    exists_transition_decomposition_of_support_le_two
      hp hcap htpos htone hlam
      s₂ Cs₂ (by rw [hs2Support]; omega)
  obtain ⟨H₂,hH₂qe⟩ :=
    exists_highExponentTransitionIntervalCertificate_of_decomposition
      hp htpos s₂ Cs₂ first₂ rest₂ pre₂ post₂ qe₂
      hrays₂ hqe₂0 hq₂ hsign₂

  let HO₁ :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        o₁ Co₁ (by rw [ho1Second]; omega))
  let HO₂ :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        o₂ Co₂ (by rw [ho2Second]; omega))

  have hqO1 : HO₁.qe = n - 1 := by
    have h :=
      highTransition_qe_eq_exponent_add_one_of_support_one
        Co₁ HO₁ ho1Support
    rw [ho1Second] at h
    omega
  have hqO2 : HO₂.qe = n - 1 := by
    have h :=
      highTransition_qe_eq_exponent_add_one_of_support_one
        Co₂ HO₂ ho2Support
    rw [ho2Second] at h
    omega

  have hpack :=
    four_transition_quotient_sum_le_two_n
      hp (by omega : 1 ≤ n)
      hdelta0 hdeltaHalf ht
      ho12 ho1s1 ho1s2 ho2s1 ho2s2 hs12
      Co₁ Co₂ Cs₁ Cs₂ HO₁ HO₂ H₁ H₂
  rw [hqO1,hqO2] at hpack
  have hH1pos : 1 ≤ H₁.qe :=
    Nat.one_le_iff_ne_zero.mpr H₁.qe_ne
  have hH2pos : 1 ≤ H₂.qe :=
    Nat.one_le_iff_ne_zero.mpr H₂.qe_ne
  have hH1one : H₁.qe = 1 := by omega
  have hH2one : H₂.qe = 1 := by omega
  have hqe1 : qe₁ = 1 := by
    rw [← hH₁qe]
    exact hH1one
  have hqe2 : qe₂ = 1 := by
    rw [← hH₂qe]
    exact hH2one

  obtain ⟨x₁,y₁,hxy₁,hlarge₁,hskinny₁⟩ :=
    support_two_unit_transition_skinny_triangle
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      s₁ Cs₁ hs1Second hs1Support
      first₁ rest₁ pre₁ post₁ qe₁
      hrays₁ hqe₁0 hq₁ hsign₁ hqe1

  obtain ⟨x₂,y₂,hxy₂,hlarge₂,hskinny₂⟩ :=
    support_two_unit_transition_skinny_triangle
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      s₂ Cs₂ hs2Second hs2Support
      first₂ rest₂ pre₂ post₂ qe₂
      hrays₂ hqe₂0 hq₂ hsign₂ hqe2

  constructor
  · exact ⟨x₁.1,y₁.1,
      by
        intro h
        apply hxy₁
        exact Subtype.ext h,
      x₁.2,y₁.2,
      hlarge₁,hskinny₁⟩
  · exact ⟨x₂.1,y₂.1,
      by
        intro h
        apply hxy₂
        exact Subtype.ext h,
      x₂.2,y₂.2,
      hlarge₂,hskinny₂⟩

#print axioms twoSupportOne_twoSupportTwo_force_two_skinny_triangles

end JSP000404Research
