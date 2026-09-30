import JSP000404Research.TransitionQuotientLargeAngle
import Mathlib.Tactic

/-!
# Large transition angle bounds the Sendov quotient

For an ordinary canonical sign transition with projective gap g,

  actual angle = pi - g.

Hence a lower bound on the genuine angle is an upper bound on the normalized
projective gap and therefore on

  floor(t*g/pi).

In the lower Sendov branch, if

  angle >= ((n-2)-2*delta)*lambda,

then

  t*g/pi <= 2+3*delta.

Thus the quotient is at most 3 for delta<1/2, and at most 2 for delta<1/3.

The same calculation is provided for the cyclic wrap transition.
-/

namespace JSP000404Research

open Real

theorem actual_angle_eq_pi_sub_ordinary_gap_of_sign_ne
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V)
    {j k : OtherVertex i}
    (horder : rayThetaAt hp i j ≤ rayThetaAt hp i k)
    (hsign : raySignAt hp i j ≠ raySignAt hp i k) :
    EuclideanGeometry.angle (p j.1) (p i) (p k.1) =
      Real.pi - (rayThetaAt hp i k - rayThetaAt hp i j) := by
  have hspan :
      rayThetaAt hp i k - rayThetaAt hp i j ≤ Real.pi :=
    (canonical_parameter_gap_bounds hp i horder).2
  have habs :
      |rayThetaAt hp i j - rayThetaAt hp i k| =
        rayThetaAt hp i k - rayThetaAt hp i j := by
    rw [abs_of_nonpos]
    · ring
    · linarith
  change
    InnerProductGeometry.angle
        (p j.1 - p i) (p k.1 - p i) =
      Real.pi - (rayThetaAt hp i k - rayThetaAt hp i j)
  rw [rayRepAt_eq hp i j, rayRepAt_eq hp i k,
      angle_positive_smul_signedRay
        (rayRhoAt_pos hp i j) (rayRhoAt_pos hp i k),
      angle_signedRayDirection_eq_pi_sub_of_sign_ne
        hsign]
  · rw [habs]
  · rw [habs]
    exact hspan

theorem ordinary_transition_quotient_le_three_of_large_angle
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {n : ℕ} {delta t lam : ℝ}
    (hn2 : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    {j k : OtherVertex i}
    (horder : rayThetaAt hp i j ≤ rayThetaAt hp i k)
    (hsign : raySignAt hp i j ≠ raySignAt hp i k)
    (hlarge :
      (((n - 2 : ℕ) : ℝ) - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p j.1) (p i) (p k.1)) :
    Nat.floor
        (t * ((rayThetaAt hp i k -
          rayThetaAt hp i j) / Real.pi)) ≤ 3 := by
  have htpos :
      0 < t := by
    rw [ht]
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hang :=
    actual_angle_eq_pi_sub_ordinary_gap_of_sign_ne
      hp i horder hsign
  rw [hang, hlam] at hlarge
  have hpi : 0 < Real.pi := Real.pi_pos
  have hgap0 :
      0 ≤ rayThetaAt hp i k - rayThetaAt hp i j := by
    linarith
  have hncast :
      ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn2]
    norm_num
  rw [hncast, ht] at hlarge
  have hnorm :
      t * ((rayThetaAt hp i k -
          rayThetaAt hp i j) / Real.pi) < 4 := by
    have htne : t ≠ 0 := ne_of_gt htpos
    field_simp [htne, ne_of_gt hpi] at hlarge ⊢
    nlinarith
  have hnonneg :
      0 ≤ t * ((rayThetaAt hp i k -
          rayThetaAt hp i j) / Real.pi) := by
    positivity
  have hfloorLt :
      Nat.floor
          (t * ((rayThetaAt hp i k -
            rayThetaAt hp i j) / Real.pi)) < 4 := by
    apply (Nat.floor_lt hnonneg).2
    exact_mod_cast hnorm
  omega

theorem ordinary_transition_quotient_le_two_of_large_angle
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {n : ℕ} {delta t lam : ℝ}
    (hn2 : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaThird : delta < (1 : ℝ) / 3)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    {j k : OtherVertex i}
    (horder : rayThetaAt hp i j ≤ rayThetaAt hp i k)
    (hsign : raySignAt hp i j ≠ raySignAt hp i k)
    (hlarge :
      (((n - 2 : ℕ) : ℝ) - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p j.1) (p i) (p k.1)) :
    Nat.floor
        (t * ((rayThetaAt hp i k -
          rayThetaAt hp i j) / Real.pi)) ≤ 2 := by
  have htpos :
      0 < t := by
    rw [ht]
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hang :=
    actual_angle_eq_pi_sub_ordinary_gap_of_sign_ne
      hp i horder hsign
  rw [hang, hlam] at hlarge
  have hpi : 0 < Real.pi := Real.pi_pos
  have hncast :
      ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn2]
    norm_num
  rw [hncast, ht] at hlarge
  have hnorm :
      t * ((rayThetaAt hp i k -
          rayThetaAt hp i j) / Real.pi) < 3 := by
    have htne : t ≠ 0 := ne_of_gt htpos
    field_simp [htne, ne_of_gt hpi] at hlarge ⊢
    nlinarith
  have hnonneg :
      0 ≤ t * ((rayThetaAt hp i k -
          rayThetaAt hp i j) / Real.pi) := by
    have hgap0 :
        0 ≤ rayThetaAt hp i k - rayThetaAt hp i j := by linarith
    positivity
  have hfloorLt :
      Nat.floor
          (t * ((rayThetaAt hp i k -
            rayThetaAt hp i j) / Real.pi)) < 3 := by
    apply (Nat.floor_lt hnonneg).2
    exact_mod_cast hnorm
  omega

/-- Wrap transition form.  The lifted transition condition means the raw
canonical signs of first and last agree, so the actual angle is the complement
of the wrap projective gap. -/
theorem wrap_transition_quotient_le_three_of_large_angle
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {n : ℕ} {delta t lam : ℝ}
    (hn2 : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    {first last : OtherVertex i}
    (horder : rayThetaAt hp i first ≤ rayThetaAt hp i last)
    (htransition :
      raySignAt hp i last ≠ !raySignAt hp i first)
    (hlarge :
      (((n - 2 : ℕ) : ℝ) - 2 * delta) * lam ≤
        EuclideanGeometry.angle (p last.1) (p i) (p first.1)) :
    Nat.floor
        (t * ((rayThetaAt hp i first + Real.pi -
          rayThetaAt hp i last) / Real.pi)) ≤ 3 := by
  have hsame :
      raySignAt hp i last = raySignAt hp i first := by
    cases hf : raySignAt hp i first <;>
      cases hl : raySignAt hp i last <;>
      simp_all
  have hang :
      EuclideanGeometry.angle (p last.1) (p i) (p first.1) =
        rayThetaAt hp i last - rayThetaAt hp i first := by
    have hcomm :
        EuclideanGeometry.angle (p last.1) (p i) (p first.1) =
          EuclideanGeometry.angle (p first.1) (p i) (p last.1) :=
      EuclideanGeometry.angle_comm _ _ _
    rw [hcomm]
    exact actual_angle_eq_ordinary_projective_gap_of_sign_eq
      hp i horder hsame.symm
  have htpos :
      0 < t := by
    rw [ht]
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hncast :
      ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn2]
    norm_num
  rw [hang, hlam, hncast, ht] at hlarge
  have hnorm :
      t * ((rayThetaAt hp i first + Real.pi -
          rayThetaAt hp i last) / Real.pi) < 4 := by
    have htne : t ≠ 0 := ne_of_gt htpos
    field_simp [htne, ne_of_gt hpi] at hlarge ⊢
    nlinarith
  have hfirst0 := rayThetaAt_nonneg hp i first
  have hlastPi := rayThetaAt_lt_pi hp i last
  have hgap0 :
      0 ≤ rayThetaAt hp i first + Real.pi -
        rayThetaAt hp i last := by
    linarith
  have hnonneg :
      0 ≤ t * ((rayThetaAt hp i first + Real.pi -
          rayThetaAt hp i last) / Real.pi) := by
    positivity
  have hfloorLt :
      Nat.floor
          (t * ((rayThetaAt hp i first + Real.pi -
            rayThetaAt hp i last) / Real.pi)) < 4 := by
    apply (Nat.floor_lt hnonneg).2
    exact_mod_cast hnorm
  omega

#print axioms actual_angle_eq_pi_sub_ordinary_gap_of_sign_ne
#print axioms ordinary_transition_quotient_le_three_of_large_angle
#print axioms ordinary_transition_quotient_le_two_of_large_angle
#print axioms wrap_transition_quotient_le_three_of_large_angle

end JSP000404Research
