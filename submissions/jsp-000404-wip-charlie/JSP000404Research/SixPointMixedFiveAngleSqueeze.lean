import JSP000404Research.HamiltonianResidualConsequences
import JSP000404Research.HamiltonianResidualBaseTriangle
import JSP000404Research.MixedSupportThreeSmallMatchings
import Mathlib.Tactic

/-!
# Five simultaneous angle inequalities for the surviving six-centre mixed branch

The support-one minimum and uncompensated-minimum-deletion assumptions force
two support-three middle-hidden small perfect matchings. Their finite
Hamiltonian residual classification and the two distinct planar cross/base
separation arguments apply to THE SAME x,y,z, rather than to independently
chosen witness triples.

Necessary conditions only. Neither the existence of the resulting planar
configuration nor the global Boolean-hole payment is resolved here.
-/

namespace JSP000404Research

theorem six_point_mixed_no_minimum_deletion_five_angle_squeeze
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
    (hMin : ∀ v : V, v ≠ top →
      centreExponent (C v) t = n - 3)
    (hsupA : positiveSupport (centreQuotient (C a) t) = 1)
    (hNoMin :
      SixPointNoCompensatedMinimumDeletion
        C (by rw [hcard]; omega) top t n) :
    ∃ b c x y z : V,
      b ≠ top ∧ c ≠ top ∧ b ≠ a ∧ c ≠ a ∧ b ≠ c ∧
      x ≠ top ∧ y ≠ top ∧ z ≠ top ∧
      x ≠ b ∧ y ≠ b ∧ z ≠ b ∧
      x ≠ c ∧ y ≠ c ∧ z ≠ c ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      EuclideanGeometry.angle (p c) (p b) (p x) +
        EuclideanGeometry.angle (p y) (p b) (p z) ≤ delta * lam ∧
      EuclideanGeometry.angle (p b) (p c) (p y) +
        EuclideanGeometry.angle (p x) (p c) (p z) ≤ delta * lam ∧
      (1 - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p x) (p b) (p z) ∧
      (1 - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p y) (p c) (p z) ∧
      (1 - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p c) (p b) (p z) ∧
      (1 - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p b) (p c) (p z) ∧
      EuclideanGeometry.angle (p b) (p z) (p c) ≤
        Real.pi - 2 * (1 - 2 * delta) * lam := by
  obtain ⟨b, c, hbTop, hcTop, hbA, hcA, hbc,
      _hbsup, _hcsup, ⟨Mb⟩, ⟨Mc⟩⟩ :=
    mixed_support_one_has_two_smallPerfectMatchings
      hp hcap C hcard hn5 hdelta0 hdeltaHalf ht hlam
      top a hta hTop hMin hsupA hNoMin
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  obtain ⟨x, y, z,
      hxTop, hyTop, hzTop,
      hxB, hyB, hzB, hxC, hyC, hzC,
      hxy, hxz, hyz,
      hB, hC, hCrossB, hCrossC⟩ :=
    two_smallPerfectMatchings_hamiltonian_with_cross_separation
      hp hcap hcard hdelta0 hdeltaHalf hlampos
      hbTop hcTop hbc Mb Mc
  obtain ⟨hBaseB, hBaseC, hApex⟩ :=
    hamiltonian_residual_base_triangle_bounds
      hp hcap hbc
      hyB.symm hyC.symm hxB.symm hxC.symm hzB.symm hzC.symm
      hB hC
  exact ⟨b, c, x, y, z,
    hbTop, hcTop, hbA, hcA, hbc,
    hxTop, hyTop, hzTop,
    hxB, hyB, hzB, hxC, hyC, hzC,
    hxy, hxz, hyz,
    hB, hC, hCrossB, hCrossC, hBaseB, hBaseC, hApex⟩

#print axioms six_point_mixed_no_minimum_deletion_five_angle_squeeze

end JSP000404Research
