import JSP000404Research.CentreExponent
import JSP000404Research.SignedRayAngle
import JSP000404Research.SharpCentre
import Mathlib.Tactic

/-!
# Positive quotient forced by an actual canonical sign change

For two rays from the same centre, sorted by canonical projective parameter,
opposite canonical signs make their genuine Euclidean angle supplementary to
their projective separation.

Under the global Sendov cap angle <= pi-lambda, with lambda=pi/t, the normalized
projective gap therefore satisfies

  1 <= t * gap.

Hence its natural quotient floor(t*gap) is nonzero.

This is the local geometric input required to prove that the actual centre
sign path changes only across positive quotient gaps.
-/

namespace JSP000404Research

open Real

/-- Distinct non-centre subtype vertices have distinct underlying vertices. -/
theorem otherVertex_val_ne
    {V : Type*} {i : V}
    {j k : OtherVertex i}
    (hjk : j ≠ k) :
    j.1 ≠ k.1 := by
  intro h
  apply hjk
  exact Subtype.ext h

/-- The projective parameter difference of two canonical rays lies in [0,pi]
whenever the rays are theta-ordered. -/
theorem canonical_parameter_gap_bounds
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V)
    {j k : OtherVertex i}
    (horder : rayThetaAt hp i j ≤ rayThetaAt hp i k) :
    0 ≤ rayThetaAt hp i k - rayThetaAt hp i j ∧
      rayThetaAt hp i k - rayThetaAt hp i j ≤ Real.pi := by
  constructor
  · linarith
  · have hj0 := rayThetaAt_nonneg hp i j
    have hkpi := rayThetaAt_lt_pi hp i k
    linarith [Real.pi_pos]

/-- Actual canonical sign change across an ordered ray pair forces at least one
normalized cap unit of projective separation. -/
theorem one_le_t_mul_gap_of_canonical_sign_ne
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    {j k : OtherVertex i}
    (hjk : j ≠ k)
    (horder : rayThetaAt hp i j ≤ rayThetaAt hp i k)
    (hsign : raySignAt hp i j ≠ raySignAt hp i k) :
    1 ≤
      t * ((rayThetaAt hp i k - rayThetaAt hp i j) / Real.pi) := by
  have hji : j.1 ≠ i := j.2
  have hki : k.1 ≠ i := k.2
  have hjkVal : j.1 ≠ k.1 := otherVertex_val_ne hjk
  have hcap' :=
    hcap j.1 i k.1 hji hjkVal (Ne.symm hki)
  change
    InnerProductGeometry.angle
        (p j.1 - p i) (p k.1 - p i)
      ≤ Real.pi - lam at hcap'
  rw [rayRepAt_eq hp i j, rayRepAt_eq hp i k] at hcap'
  have hbounds :=
    canonical_parameter_gap_bounds hp i horder
  exact one_le_t_mul_normalized_gap_of_opposite_signs
    (rayRhoAt_pos hp i j)
    (rayRhoAt_pos hp i k)
    ht hlam horder hbounds.2 hsign hcap'

/-- Therefore the natural Sendov quotient of that normalized gap is positive. -/
theorem floor_t_mul_gap_ne_zero_of_canonical_sign_ne
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    {j k : OtherVertex i}
    (hjk : j ≠ k)
    (horder : rayThetaAt hp i j ≤ rayThetaAt hp i k)
    (hsign : raySignAt hp i j ≠ raySignAt hp i k) :
    Nat.floor
        (t * ((rayThetaAt hp i k - rayThetaAt hp i j) / Real.pi))
      ≠ 0 := by
  have hone :=
    one_le_t_mul_gap_of_canonical_sign_ne
      hp hcap ht hlam i hjk horder hsign
  have hnonneg :
      0 ≤
        t * ((rayThetaAt hp i k - rayThetaAt hp i j) / Real.pi) := by
    linarith
  have hfloor :
      1 ≤ Nat.floor
        (t * ((rayThetaAt hp i k - rayThetaAt hp i j) / Real.pi)) := by
    exact (Nat.le_floor hnonneg).2 (by
      exact_mod_cast hone)
  omega

#print axioms one_le_t_mul_gap_of_canonical_sign_ne
#print axioms floor_t_mul_gap_ne_zero_of_canonical_sign_ne

end JSP000404Research
