
import JSP000404Research.ExactWitnessProjectiveDistance
import JSP000404Research.CanonicalSignGap
import JSP000404Research.SmallSameSignGapAngle
import Mathlib.Tactic

/-!
# The short projective arc of an exact maximum-angle witness is empty

Let W=(a,b,c) attain the global angle cap

  angle(a,b,c) = pi-lambda,

with lambda=pi/t and t>2.

The projective distance between the two witness rays at b is exactly lambda.
After ordering their canonical parameters, the short projective arc is
therefore either

  theta_c - theta_a = lambda

or the cyclic wrap arc

  theta_a + pi - theta_c = lambda.

In either case there is no third canonical ray parameter strictly inside that
short arc.

Reason: the exact witness endpoints realize the supplementary branch, hence
the lifted endpoint signs differ across the short arc.  Any intermediate ray
must differ in sign from at least one adjacent endpoint.  The global angle cap
then forces that proper subarc to have scaled length at least one, while it is
strictly shorter than the whole exact unit arc.  Contradiction.

This upgrades an exact maximum-angle witness to an empty projective short arc.
-/

namespace JSP000404Research

open Real

theorem scaled_gap_lt_one_of_lt_lam
    {t lam d : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hd : d < lam) :
    t * (d / Real.pi) < 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have htpi : 0 < t / Real.pi := div_pos ht hpi
  have hrewrite :
      t * (d / Real.pi) = (t / Real.pi) * d := by ring
  have hlamScale :
      (t / Real.pi) * lam = 1 := by
    rw [hlam]
    field_simp [ne_of_gt ht, Real.pi_ne_zero]
  rw [hrewrite]
  rw [← hlamScale]
  exact mul_lt_mul_of_pos_left hd htpi

/-- Ordered endpoint form of the exact short-arc dichotomy. -/
theorem exactWitness_ordered_short_gap_or_wrap_eq_lam
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (horder :
      rayThetaAt hp W.b
          (⟨W.a, W.hab⟩ : OtherVertex W.b)
        ≤
      rayThetaAt hp W.b
          (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b)) :
    (rayThetaAt hp W.b
          (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b)
        -
      rayThetaAt hp W.b
          (⟨W.a, W.hab⟩ : OtherVertex W.b) = lam)
    ∨
    (rayThetaAt hp W.b
          (⟨W.a, W.hab⟩ : OtherVertex W.b)
        + Real.pi -
      rayThetaAt hp W.b
          (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b) = lam) := by
  let ja : OtherVertex W.b := ⟨W.a, W.hab⟩
  let kc : OtherVertex W.b := ⟨W.c, W.hbc.symm⟩
  have hdist :=
    exactWitness_projectiveDistance_eq_lam
      hp hn hdelta0 ht hlam W
  have habs :
      |rayThetaAt hp W.b ja - rayThetaAt hp W.b kc|
        =
      rayThetaAt hp W.b kc - rayThetaAt hp W.b ja := by
    rw [abs_of_nonpos]
    · ring
    · exact horder
  dsimp [ja, kc] at hdist ⊢
  rw [projectiveRayDistance, habs] at hdist
  by_cases hshort :
      rayThetaAt hp W.b
            (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b)
          -
        rayThetaAt hp W.b
            (⟨W.a, W.hab⟩ : OtherVertex W.b)
      ≤
      Real.pi -
        (rayThetaAt hp W.b
            (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b)
          -
         rayThetaAt hp W.b
            (⟨W.a, W.hab⟩ : OtherVertex W.b))
  · left
    rw [min_eq_left hshort] at hdist
    exact hdist
  · right
    have hrev :
        Real.pi -
            (rayThetaAt hp W.b
                (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b)
              -
             rayThetaAt hp W.b
                (⟨W.a, W.hab⟩ : OtherVertex W.b))
          ≤
        rayThetaAt hp W.b
              (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b)
            -
          rayThetaAt hp W.b
              (⟨W.a, W.hab⟩ : OtherVertex W.b) :=
      le_of_not_ge hshort
    rw [min_eq_right hrev] at hdist
    linarith

/-- In the ordinary-short-arc case the witness endpoint canonical signs are
opposite. -/
theorem exactWitness_ordinary_short_endpoint_sign_ne
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (horder :
      rayThetaAt hp W.b
          (⟨W.a, W.hab⟩ : OtherVertex W.b)
        ≤
      rayThetaAt hp W.b
          (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b))
    (hgap :
      rayThetaAt hp W.b
          (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b)
        -
      rayThetaAt hp W.b
          (⟨W.a, W.hab⟩ : OtherVertex W.b) = lam) :
    raySignAt hp W.b
        (⟨W.a, W.hab⟩ : OtherVertex W.b)
      ≠
    raySignAt hp W.b
        (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b) := by
  intro hsign
  let ja : OtherVertex W.b := ⟨W.a, W.hab⟩
  let kc : OtherVertex W.b := ⟨W.c, W.hbc.symm⟩
  have hangle :=
    actual_angle_eq_ordinary_projective_gap_of_sign_eq
      hp W.b (j := ja) (k := kc) horder hsign
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlamHalf : lam < Real.pi / 2 := by
    rw [hlam]
    apply (div_lt_iff₀ htpos).2
    have htTwo : 2 < t := by
      rw [ht]
      have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    nlinarith [Real.pi_pos]
  have hangle' :
      EuclideanGeometry.angle (p W.a) (p W.b) (p W.c) = lam := by
    simpa [ja, kc, hgap] using hangle
  rw [W.exact] at hangle'
  linarith

/-- No third canonical parameter lies strictly inside an ordinary exact
witness short arc. -/
theorem no_ray_strictly_inside_exactWitness_ordinary_short_arc
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (x : OtherVertex W.b)
    (hleft :
      rayThetaAt hp W.b
          (⟨W.a, W.hab⟩ : OtherVertex W.b)
        <
      rayThetaAt hp W.b x)
    (hright :
      rayThetaAt hp W.b x
        <
      rayThetaAt hp W.b
          (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b))
    (hgap :
      rayThetaAt hp W.b
          (⟨W.c, W.hbc.symm⟩ : OtherVertex W.b)
        -
      rayThetaAt hp W.b
          (⟨W.a, W.hab⟩ : OtherVertex W.b) = lam) :
    False := by
  let ja : OtherVertex W.b := ⟨W.a, W.hab⟩
  let kc : OtherVertex W.b := ⟨W.c, W.hbc.symm⟩
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hendNe :
      raySignAt hp W.b ja ≠ raySignAt hp W.b kc :=
    exactWitness_ordinary_short_endpoint_sign_ne
      hp hn hdelta0 ht hlam W
      (by linarith) (by simpa [ja, kc] using hgap)
  by_cases hjx :
      raySignAt hp W.b ja ≠ raySignAt hp W.b x
  · have hjxRay : ja ≠ x := by
      intro h
      subst x
      linarith
    have hone :=
      one_le_t_mul_gap_of_canonical_sign_ne
        hp hcap htpos hlam W.b
        hjxRay (by linarith) hjx
    have hsub :
        rayThetaAt hp W.b x - rayThetaAt hp W.b ja < lam := by
      dsimp [ja, kc] at hleft hright hgap ⊢
      linarith
    have hlt :=
      scaled_gap_lt_one_of_lt_lam htpos hlam hsub
    linarith
  · have hjxEq :
      raySignAt hp W.b ja = raySignAt hp W.b x :=
      Classical.not_not.mp hjx
    have hxk :
      raySignAt hp W.b x ≠ raySignAt hp W.b kc := by
      intro hxkEq
      apply hendNe
      exact hjxEq.trans hxkEq
    have hxkRay : x ≠ kc := by
      intro h
      subst x
      linarith
    have hone :=
      one_le_t_mul_gap_of_canonical_sign_ne
        hp hcap htpos hlam W.b
        hxkRay (by linarith) hxk
    have hsub :
        rayThetaAt hp W.b kc - rayThetaAt hp W.b x < lam := by
      dsimp [ja, kc] at hleft hright hgap ⊢
      linarith
    have hlt :=
      scaled_gap_lt_one_of_lt_lam htpos hlam hsub
    linarith

#print axioms scaled_gap_lt_one_of_lt_lam
#print axioms exactWitness_ordered_short_gap_or_wrap_eq_lam
#print axioms no_ray_strictly_inside_exactWitness_ordinary_short_arc

end JSP000404Research
