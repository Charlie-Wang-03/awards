import JSP000404Research.MixedSupportThreeSmallMatchings
import JSP000404Research.HamiltonianResidualSeparation
import Mathlib.Tactic

/-!
# Strengthened terminal for two small perfect matchings

This file connects the finite matching classification to the geometric
cross-separation lemma.

The existing classification gives a Hamiltonian residual on the three
remaining minima x,y,z.  The two matching-sum inequalities then force the
cross angles x-b-z and y-c-z to be at least
(1-2*delta)*lambda.

This is still a terminal refinement, not a contradiction.
-/

namespace JSP000404Research

open Real

theorem two_smallPerfectMatchings_hamiltonian_with_cross_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {top b c : V} {delta lam : ℝ}
    (hcard : Fintype.card V = 6)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlam : 0 < lam)
    (hbTop : b ≠ top)
    (hcTop : c ≠ top)
    (hbc : b ≠ c)
    (Mb : SmallPerfectMatchingAwayFromTop
      (p := p) top b delta lam)
    (Mc : SmallPerfectMatchingAwayFromTop
      (p := p) top c delta lam) :
    ∃ x y z : V,
      x ≠ top ∧ y ≠ top ∧ z ≠ top ∧
      x ≠ b ∧ y ≠ b ∧ z ≠ b ∧
      x ≠ c ∧ y ≠ c ∧ z ≠ c ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      EuclideanGeometry.angle (p c) (p b) (p x) +
          EuclideanGeometry.angle (p y) (p b) (p z)
        ≤ delta * lam ∧
      EuclideanGeometry.angle (p b) (p c) (p y) +
          EuclideanGeometry.angle (p x) (p c) (p z)
        ≤ delta * lam ∧
      (1 - 2 * delta) * lam ≤
          EuclideanGeometry.angle (p x) (p b) (p z) ∧
      (1 - 2 * delta) * lam ≤
          EuclideanGeometry.angle (p y) (p c) (p z) := by
  obtain ⟨x,y,z,
      hxTop,hyTop,hzTop,
      hxB,hyB,hzB,
      hxC,hyC,hzC,
      hxy,hxz,hyz,
      hsmallB,hsmallC⟩ :=
    SmallPerfectMatchingAwayFromTop.two_smallPerfectMatchings_hamiltonian_residual
      hp hcap hcard hdelta0 hdeltaHalf hlam
      hbTop hcTop hbc Mb Mc

  have hsep :=
    hamiltonian_residual_cross_separation
      hp hcap
      hbc
      hxB.symm hyB.symm
      hxC.symm hyC.symm
      hsmallB hsmallC

  exact ⟨x,y,z,
    hxTop,hyTop,hzTop,
    hxB,hyB,hzB,
    hxC,hyC,hzC,
    hxy,hxz,hyz,
    hsmallB,hsmallC,
    hsep.1,hsep.2⟩

#print axioms two_smallPerfectMatchings_hamiltonian_with_cross_separation

end JSP000404Research
