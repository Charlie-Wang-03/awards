
import JSP000404Research.ExactAngleWitnessRestriction
import JSP000404Research.SignedRayAngle
import Mathlib.Tactic

/-!
# Exact maximum-angle witnesses have projective separation lambda

At a centre b, any two canonical projective ray parameters lie in [0,pi), so
their projective distance is at most pi/2.

For an exact angle witness W=(a,b,c),

  angle(a,b,c) = pi-lambda.

In the Sendov range n>=3, lambda=pi/t with t=n+delta and delta>=0 gives
lambda<pi/2.  Hence the exact witness angle is strictly larger than pi/2 and
cannot equal the projective distance.  It must be the supplementary branch.

Therefore the projective distance between rays b--a and b--c is exactly
lambda, and its t/pi-scaled width is exactly one.
-/

namespace JSP000404Research

open Real

theorem projectiveRayDistance_nonneg_of_canonical
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V)
    (j k : OtherVertex i) :
    0 ≤ projectiveRayDistance
      (rayThetaAt hp i j) (rayThetaAt hp i k) := by
  unfold projectiveRayDistance
  have hj0 := rayThetaAt_nonneg hp i j
  have hk0 := rayThetaAt_nonneg hp i k
  have hjpi := rayThetaAt_lt_pi hp i j
  have hkpi := rayThetaAt_lt_pi hp i k
  have habs0 :
      0 ≤ |rayThetaAt hp i j - rayThetaAt hp i k| :=
    abs_nonneg _
  have habsPi :
      |rayThetaAt hp i j - rayThetaAt hp i k| ≤ Real.pi := by
    rw [abs_le]
    constructor <;> linarith
  exact le_min habs0 (by linarith)

/-- Projective distance between canonical rays is at most pi/2. -/
theorem projectiveRayDistance_le_half_pi_of_canonical
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V)
    (j k : OtherVertex i) :
    projectiveRayDistance
      (rayThetaAt hp i j) (rayThetaAt hp i k)
      ≤ Real.pi / 2 := by
  let d :=
    |rayThetaAt hp i j - rayThetaAt hp i k|
  have hdPi : d ≤ Real.pi := by
    dsimp [d]
    have hj0 := rayThetaAt_nonneg hp i j
    have hk0 := rayThetaAt_nonneg hp i k
    have hjpi := rayThetaAt_lt_pi hp i j
    have hkpi := rayThetaAt_lt_pi hp i k
    rw [abs_le]
    constructor <;> linarith
  unfold projectiveRayDistance
  change min d (Real.pi - d) ≤ Real.pi / 2
  by_cases hd : d ≤ Real.pi / 2
  · exact (min_le_left _ _).trans hd
  · have hright : Real.pi - d < Real.pi / 2 := by
      have hd' : Real.pi / 2 < d := lt_of_not_ge hd
      linarith
    exact (min_le_right _ _).trans hright.le

/-- Abstract exact-witness form: if lambda<pi/2, the witness projective
distance is exactly lambda. -/
theorem exactWitness_projectiveDistance_eq_lam_of_lam_lt_half_pi
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam : ℝ}
    (W : ExactAngleWitness p lam)
    (hlamHalf : lam < Real.pi / 2) :
    projectiveRayDistance
        (rayThetaAt hp W.b
          (⟨W.a, W.hab⟩ : OtherVertex W.b))
        (rayThetaAt hp W.b
          (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b))
      = lam := by
  let ja : OtherVertex W.b := ⟨W.a, W.hab⟩
  let kc : OtherVertex W.b := ⟨W.c, W.hbc.symm⟩
  have hprojLe :
      projectiveRayDistance
          (rayThetaAt hp W.b ja)
          (rayThetaAt hp W.b kc)
        ≤ Real.pi / 2 :=
    projectiveRayDistance_le_half_pi_of_canonical
      hp W.b ja kc
  have hangleLarge :
      Real.pi / 2 <
        EuclideanGeometry.angle (p W.a) (p W.b) (p W.c) := by
    rw [W.exact]
    linarith
  rcases actual_angle_eq_projective_or_supplement
      hp W.b ja kc with hproj | hsupp
  · have :
        EuclideanGeometry.angle (p W.a) (p W.b) (p W.c)
          ≤ Real.pi / 2 := by
      simpa [ja, kc] using hproj.trans_le hprojLe
    linarith
  · have hsupp' :
      EuclideanGeometry.angle (p W.a) (p W.b) (p W.c)
        =
      Real.pi -
        projectiveRayDistance
          (rayThetaAt hp W.b ja)
          (rayThetaAt hp W.b kc) := by
      simpa [ja, kc] using hsupp
    rw [W.exact] at hsupp'
    linarith

/-- Sendov lower-branch specialization. -/
theorem exactWitness_projectiveDistance_eq_lam
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam) :
    projectiveRayDistance
        (rayThetaAt hp W.b
          (⟨W.a, W.hab⟩ : OtherVertex W.b))
        (rayThetaAt hp W.b
          (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b))
      = lam := by
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have htTwo : 2 < t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlamHalf : lam < Real.pi / 2 := by
    rw [hlam]
    apply (div_lt_iff₀ htpos).2
    have hpi := Real.pi_pos
    nlinarith
  exact
    exactWitness_projectiveDistance_eq_lam_of_lam_lt_half_pi
      hp W hlamHalf

/-- The exact witness short projective arc has scaled width exactly one. -/
theorem exactWitness_scaled_projectiveDistance_eq_one
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam) :
    t *
      (projectiveRayDistance
        (rayThetaAt hp W.b
          (⟨W.a, W.hab⟩ : OtherVertex W.b))
        (rayThetaAt hp W.b
          (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b))
        / Real.pi)
      = 1 := by
  rw [exactWitness_projectiveDistance_eq_lam
      hp hn hdelta0 ht hlam W, hlam]
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp [ne_of_gt htpos, Real.pi_ne_zero]

#print axioms projectiveRayDistance_le_half_pi_of_canonical
#print axioms exactWitness_projectiveDistance_eq_lam
#print axioms exactWitness_scaled_projectiveDistance_eq_one

end JSP000404Research
