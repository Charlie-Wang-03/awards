
import JSP000404Research.CanonicalSignGap
import JSP000404Research.SmallSameSignGapAngle
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Every quotient-zero adjacent gap is a genuine angle below lambda

No deficit or support hypothesis is needed for the basic zero-gap geometry.

For an ordinary ordered ray pair, floor(t*gap/pi)=0 gives scaled gap < 1.
If the canonical signs differed, CanonicalSignGap would force the same floor
to be nonzero.  Hence the signs agree, the actual Euclidean angle equals the
projective gap, and lambda=pi/t gives angle<lambda.

The same argument applies to the cyclic wrap gap after lifting the first ray
by pi and flipping its canonical sign.

This is the general geometric interpretation needed by minimum-deletion
rigidity: every zero quotient adjacent to the deleted ray supplies an actual
small angle, not merely a formal zero in the quotient list.
-/

namespace JSP000404Research

open Real

theorem projective_gap_lt_lam_of_scaled_lt_one
    {t lam d : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hd : t * (d / Real.pi) < 1) :
    d < lam := by
  have htp : 0 < t / Real.pi :=
    div_pos ht Real.pi_pos
  have hscaled :
      (t / Real.pi) * d < 1 := by
    convert hd using 1 <;> ring
  have hdiv :
      d < 1 / (t / Real.pi) := by
    apply (lt_div_iff₀ htp).2
    simpa [mul_comm] using hscaled
  have hid :
      1 / (t / Real.pi) = Real.pi / t := by
    field_simp [ne_of_gt ht, Real.pi_ne_zero]
  rw [hlam, ← hid]
  exact hdiv

/-- Ordinary adjacent quotient-zero gap gives a genuine angle < lambda. -/
theorem ordinary_zero_quotient_actual_angle_lt_lam
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    {j k : OtherVertex i}
    (hjk : j ≠ k)
    (horder :
      rayThetaAt hp i j ≤ rayThetaAt hp i k)
    (hq0 :
      Nat.floor
        (t * ((rayThetaAt hp i k -
          rayThetaAt hp i j) / Real.pi)) = 0) :
    EuclideanGeometry.angle (p j.1) (p i) (p k.1) < lam := by
  have hsign :
      raySignAt hp i j = raySignAt hp i k := by
    by_contra hne
    exact
      (floor_t_mul_gap_ne_zero_of_canonical_sign_ne
        hp hcap ht hlam i hjk horder hne) hq0
  have hscaled :
      t * ((rayThetaAt hp i k -
        rayThetaAt hp i j) / Real.pi) < 1 :=
    Nat.floor_eq_zero.mp hq0
  rw [actual_angle_eq_ordinary_projective_gap_of_sign_eq
      hp i horder hsign]
  exact projective_gap_lt_lam_of_scaled_lt_one
    ht hlam hscaled

/-- Wrap quotient-zero gap gives a genuine angle < lambda. -/
theorem wrap_zero_quotient_actual_angle_lt_lam
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    {first last : OtherVertex i}
    (hfl : first ≠ last)
    (horder :
      rayThetaAt hp i first ≤ rayThetaAt hp i last)
    (hq0 :
      Nat.floor
        (t * ((rayThetaAt hp i first + Real.pi -
          rayThetaAt hp i last) / Real.pi)) = 0) :
    EuclideanGeometry.angle (p last.1) (p i) (p first.1) < lam := by
  have hsign :
      raySignAt hp i last = !raySignAt hp i first := by
    by_contra hne
    exact
      (floor_t_mul_wrap_gap_ne_zero_of_canonical_sign_ne
        hp hcap ht hlam i hfl horder hne) hq0
  have hscaled :
      t * ((rayThetaAt hp i first + Real.pi -
        rayThetaAt hp i last) / Real.pi) < 1 :=
    Nat.floor_eq_zero.mp hq0
  rw [actual_angle_eq_wrap_projective_gap_of_lifted_sign_eq
      hp i horder hsign]
  exact projective_gap_lt_lam_of_scaled_lt_one
    ht hlam hscaled

#print axioms projective_gap_lt_lam_of_scaled_lt_one
#print axioms ordinary_zero_quotient_actual_angle_lt_lam
#print axioms wrap_zero_quotient_actual_angle_lt_lam

end JSP000404Research
