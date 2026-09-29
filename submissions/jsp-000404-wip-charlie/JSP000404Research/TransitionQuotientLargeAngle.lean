import JSP000404Research.CanonicalSignGap
import Mathlib.Tactic

/-!
# A bounded transition quotient forces a genuinely large angle

Let two canonical projective rays have opposite signs.  If their ordinary
projective gap has Sendov quotient

  q = floor(t * gap / pi)

and q <= n-2 while t = n+delta, then the projective gap is strictly below
(n-1)*lambda.  Since opposite signs turn projective separation into the
supplementary genuine angle, the actual angle is strictly larger than

  (1+delta)*lambda.

This quantitative observation is useful in the support-three middle-hidden
terminal: once the three positive quotients sum to n, each of them is at most
n-2.
-/

namespace JSP000404Research

open Real

theorem parameter_gap_lt_n_sub_one_mul_lam_of_floor_le_n_sub_two
    {n : ℕ} {delta t lam theta phi : ℝ}
    (hn2 : 2 ≤ n)
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (horder : theta ≤ phi)
    (hq :
      Nat.floor
          (t * ((phi - theta) / Real.pi))
        ≤ n - 2) :
    phi - theta < ((n - 1 : ℕ) : ℝ) * lam := by
  let g : ℝ := t * ((phi - theta) / Real.pi)
  have hglt :
      g < (Nat.floor g : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one g
    exact_mod_cast h
  have hfloor :
      Nat.floor g + 1 ≤ n - 1 := by
    dsimp [g] at hq
    omega
  have hgUpper :
      g < ((n - 1 : ℕ) : ℝ) := by
    have hfloorR :
        ((Nat.floor g + 1 : ℕ) : ℝ) ≤
          ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hfloor
    norm_num at hfloorR
    exact hglt.trans_le hfloorR
  have hpi : 0 < Real.pi := Real.pi_pos
  have hgap0 : 0 ≤ phi - theta := sub_nonneg.mpr horder
  dsimp [g] at hgUpper
  rw [hlam]
  have htne : t ≠ 0 := ne_of_gt htpos
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  field_simp [htne, hpine] at hgUpper ⊢
  nlinarith

theorem signed_transition_angle_gt_one_add_delta_mul_lam_of_floor_le
    {n : ℕ} {delta t lam theta phi : ℝ}
    {sigma tau : Bool}
    (hn2 : 2 ≤ n)
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (horder : theta ≤ phi)
    (hspan : phi - theta ≤ Real.pi)
    (hsign : sigma ≠ tau)
    (hq :
      Nat.floor
          (t * ((phi - theta) / Real.pi))
        ≤ n - 2) :
    (1 + delta) * lam <
      InnerProductGeometry.angle
        (signedRayDirection sigma theta)
        (signedRayDirection tau phi) := by
  have hgap :=
    parameter_gap_lt_n_sub_one_mul_lam_of_floor_le_n_sub_two
      hn2 htpos ht hlam horder hq
  have habs :
      |theta - phi| = phi - theta := by
    rw [abs_of_nonpos]
    · ring
    · linarith
  have hdiff : |theta - phi| ≤ Real.pi := by
    rw [habs]
    exact hspan
  rw [angle_signedRayDirection_eq_pi_sub_of_sign_ne
      hsign hdiff, habs]
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hpiEq : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  rw [hpiEq, ht]
  have hnCast :
      ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ n)
  rw [hnCast] at hgap
  nlinarith

/-- Concrete ordinary-ray version. -/
theorem actual_angle_gt_one_add_delta_mul_lam_of_transition_quotient_le
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {n : ℕ} {delta t lam : ℝ}
    (hn2 : 2 ≤ n)
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    {j k : OtherVertex i}
    (horder : rayThetaAt hp i j ≤ rayThetaAt hp i k)
    (hsign : raySignAt hp i j ≠ raySignAt hp i k)
    (hq :
      Nat.floor
          (t * ((rayThetaAt hp i k -
            rayThetaAt hp i j) / Real.pi))
        ≤ n - 2) :
    (1 + delta) * lam <
      EuclideanGeometry.angle (p j.1) (p i) (p k.1) := by
  have hspan :
      rayThetaAt hp i k - rayThetaAt hp i j ≤ Real.pi :=
    (canonical_parameter_gap_bounds hp i horder).2
  have h :=
    signed_transition_angle_gt_one_add_delta_mul_lam_of_floor_le
      hn2 htpos ht hlam horder hspan hsign hq
  change
    (1 + delta) * lam <
      InnerProductGeometry.angle
        (p j.1 - p i) (p k.1 - p i)
  rw [rayRepAt_eq hp i j, rayRepAt_eq hp i k,
      angle_positive_smul_signedRay
        (rayRhoAt_pos hp i j) (rayRhoAt_pos hp i k)]
  exact h


/-- Wrap-gap analogue.  A lifted sign transition at the wrap means that the
last and first canonical signs are equal.  Thus the genuine angle is the
supplement of the wrap projective gap, and the same quotient bound gives the
same strict lower bound. -/
theorem actual_angle_gt_one_add_delta_mul_lam_of_wrap_transition_quotient_le
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {n : ℕ} {delta t lam : ℝ}
    (hn2 : 2 ≤ n)
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    {first last : OtherVertex i}
    (horder : rayThetaAt hp i first ≤ rayThetaAt hp i last)
    (htransition :
      raySignAt hp i last ≠ !raySignAt hp i first)
    (hq :
      Nat.floor
          (t * ((rayThetaAt hp i first + Real.pi -
            rayThetaAt hp i last) / Real.pi))
        ≤ n - 2) :
    (1 + delta) * lam <
      EuclideanGeometry.angle (p last.1) (p i) (p first.1) := by
  have hsame :
      raySignAt hp i last = raySignAt hp i first := by
    cases hfirst : raySignAt hp i first <;>
      cases hlast : raySignAt hp i last <;>
      simp_all
  have hfirst0 := rayThetaAt_nonneg hp i first
  have hlastPi := rayThetaAt_lt_pi hp i last
  have hwrapOrder :
      rayThetaAt hp i last ≤
        rayThetaAt hp i first + Real.pi := by
    linarith
  have hgap :=
    parameter_gap_lt_n_sub_one_mul_lam_of_floor_le_n_sub_two
      hn2 htpos ht hlam hwrapOrder hq
  have hang :
      EuclideanGeometry.angle (p first.1) (p i) (p last.1) =
        rayThetaAt hp i last - rayThetaAt hp i first :=
    actual_angle_eq_ordinary_projective_gap_of_sign_eq
      hp i horder hsame
  have hcomm :
      EuclideanGeometry.angle (p last.1) (p i) (p first.1) =
        EuclideanGeometry.angle (p first.1) (p i) (p last.1) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcomm, hang]
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hpiEq : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  rw [hpiEq, ht] at hgap
  have hnCast :
      ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ n)
  rw [hnCast] at hgap
  nlinarith

#print axioms parameter_gap_lt_n_sub_one_mul_lam_of_floor_le_n_sub_two
#print axioms signed_transition_angle_gt_one_add_delta_mul_lam_of_floor_le
#print axioms actual_angle_gt_one_add_delta_mul_lam_of_transition_quotient_le
#print axioms actual_angle_gt_one_add_delta_mul_lam_of_wrap_transition_quotient_le

end JSP000404Research
