import JSP000404Research.CanonicalProjectiveRay
import Mathlib.Tactic

/-!
# Canonical finite ray data around one centre

For a fixed centre i of an injective finite planar configuration, package every
other vertex j with the canonical projective representation of p j - p i.

The resulting data expose concrete functions

  rho j > 0,
  sigma j : Bool,
  theta j in [0,pi),

together with the exact displacement identity.  This removes all existential
choices before the later angular sorting and cyclic-gap construction.
-/

namespace JSP000404Research

open Real

/-- Vertices different from a fixed centre. -/
abbrev OtherVertex {V : Type*} (i : V) := {j : V // j ≠ i}

/-- One chosen signed projective representation of a nonzero planar vector. -/
structure ProjectiveRayRep (x : Plane) where
  rho : ℝ
  sigma : Bool
  theta : ℝ
  rho_pos : 0 < rho
  theta_nonneg : 0 ≤ theta
  theta_lt_pi : theta < Real.pi
  eq_smul : x = rho • signedRayDirection sigma theta

/-- Every nonzero plane vector has a packaged canonical projective
representation. -/
noncomputable def canonicalRayRep
    (x : Plane) (hx : x ≠ 0) :
    ProjectiveRayRep x := by
  classical
  obtain ⟨rho, sigma, theta, hrho, htheta0, hthetapi, hrepr⟩ :=
    exists_canonical_projective_representation hx
  exact
    { rho := rho
      sigma := sigma
      theta := theta
      rho_pos := hrho
      theta_nonneg := htheta0
      theta_lt_pi := hthetapi
      eq_smul := hrepr }

/-- The displacement from the centre to every other vertex is nonzero. -/
theorem displacement_ne_zero
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (j : OtherVertex i) :
    p j.1 - p i ≠ 0 := by
  intro hzero
  have hpi : p j.1 = p i := sub_eq_zero.mp hzero
  exact j.2 (hp hpi)

/-- Canonical projective ray data around a fixed centre. -/
noncomputable def rayRepAt
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (j : OtherVertex i) :
    ProjectiveRayRep (p j.1 - p i) :=
  canonicalRayRep (p j.1 - p i) (displacement_ne_zero hp i j)

noncomputable def rayRhoAt
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (j : OtherVertex i) : ℝ :=
  (rayRepAt hp i j).rho

noncomputable def raySignAt
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (j : OtherVertex i) : Bool :=
  (rayRepAt hp i j).sigma

noncomputable def rayThetaAt
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (j : OtherVertex i) : ℝ :=
  (rayRepAt hp i j).theta

theorem rayRhoAt_pos
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (j : OtherVertex i) :
    0 < rayRhoAt hp i j :=
  (rayRepAt hp i j).rho_pos

theorem rayThetaAt_nonneg
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (j : OtherVertex i) :
    0 ≤ rayThetaAt hp i j :=
  (rayRepAt hp i j).theta_nonneg

theorem rayThetaAt_lt_pi
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (j : OtherVertex i) :
    rayThetaAt hp i j < Real.pi :=
  (rayRepAt hp i j).theta_lt_pi

theorem rayRepAt_eq
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (j : OtherVertex i) :
    p j.1 - p i =
      rayRhoAt hp i j •
        signedRayDirection (raySignAt hp i j) (rayThetaAt hp i j) :=
  (rayRepAt hp i j).eq_smul

#print axioms canonicalRayRep
#print axioms displacement_ne_zero
#print axioms rayRhoAt_pos
#print axioms rayThetaAt_nonneg
#print axioms rayThetaAt_lt_pi
#print axioms rayRepAt_eq

end JSP000404Research
