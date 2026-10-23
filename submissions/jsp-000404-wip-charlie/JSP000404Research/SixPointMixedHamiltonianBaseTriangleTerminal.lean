import JSP000404Research.MixedSupportThreeSmallMatchings
import JSP000404Research.HamiltonianResidualBaseTriangle
import Mathlib.Tactic

/-!
# Mixed six-centre hard profile forces a quantitative base triangle

The support-one/no-compensated-minimum-deletion branch produces two
non-top support-three centres with delta-small perfect matchings.
Their mutual partner classification gives a three-minimum Hamiltonian
residual pattern. Combining this with the checked base-triangle squeeze
produces an original-geometry necessary condition with no new analytic
assumptions.

This does not assert that such a triangle is impossible; the original
global Boolean-hole payment is not derived here.
-/

namespace JSP000404Research

theorem six_point_mixed_no_minimum_deletion_has_base_triangle_squeeze
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top a : V)
    (hta : top ≠ a)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hsupA : positiveSupport (centreQuotient (C a) t) = 1)
    (hNoMin :
      SixPointNoCompensatedMinimumDeletion
        C (by rw [hcard]; omega) top t n) :
    ∃ b c z : V,
      b ≠ top ∧ c ≠ top ∧
      b ≠ a ∧ c ≠ a ∧ b ≠ c ∧
      z ≠ top ∧ z ≠ b ∧ z ≠ c ∧
      (1 - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p c) (p b) (p z) ∧
      (1 - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p b) (p c) (p z) ∧
      EuclideanGeometry.angle (p b) (p z) (p c) ≤
        Real.pi - 2 * (1 - 2 * delta) * lam := by
  obtain ⟨b, c, hbTop, hcTop, hbA, hcA, hbc,
      _hbSup, _hcSup, ⟨Mb⟩, ⟨Mc⟩⟩ :=
    mixed_support_one_has_two_smallPerfectMatchings
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top a hta hTop hMin hsupA hNoMin

  have htpos : 0 < t := by
    rw [ht]
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos

  obtain ⟨x, y, z,
      hzTopX, hyTop, hzTop,
      hxB, hyB, hzB,
      hxC, hyC, hzC,
      _hxy, _hxz, _hyz,
      hB, hC⟩ :=
    SmallPerfectMatchingAwayFromTop.two_smallPerfectMatchings_hamiltonian_residual
      hp hcap hcard hdelta0 hdeltaHalf hlampos
      hbTop hcTop hbc Mb Mc

  obtain ⟨hBaseB, hBaseC, hApex⟩ :=
    hamiltonian_residual_base_triangle_bounds
      hp hcap hbc hyB hyC hxB hxC hzB hzC hB hC

  exact ⟨b, c, z, hbTop, hcTop, hbA, hcA, hbc,
    hzTop, hzB, hzC, hBaseB, hBaseC, hApex⟩

#print axioms six_point_mixed_no_minimum_deletion_has_base_triangle_squeeze

end JSP000404Research
