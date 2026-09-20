import JSP000404Research.StrictExposure
import JSP000404Research.TransitionRotation
import JSP000404Research.FiniteProjectiveRays
import Mathlib.Tactic

/-!
# Exposure from an ordinary one-transition split of the actual ray cycle

Suppose the canonical projective rays around a centre are divided at one
ordinary positive gap into two nonempty blocks.

* every ray in the first block has sign a;
* every ray in the second block has sign !a;
* all first-block parameters are at most theta_left;
* all second-block parameters are at least theta_right;
* theta_left < theta_right.

Represent the second block canonically.  Represent the first block after adding
pi to every parameter and flipping the sign.  Every actual ray then has the
common sign !a and lies in the interval

  [theta_right, theta_left + pi],

whose width is pi-(theta_right-theta_left)<pi.  Hence the centre is strictly
exposed.

This theorem contains the whole Euclidean geometry of the ordinary-transition
case.  Remaining work is only to extract the two blocks from the concrete
cyclic sign / quotient decomposition.
-/

namespace JSP000404Research

open Real

/-- Ordinary positive-transition split gives strict exposure. -/
theorem strictlyExposedAt_of_two_sign_blocks
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i : V}
    (sigma : Bool)
    (before after : List (OtherVertex i))
    (hcover :
      ∀ j : OtherVertex i, j ∈ before ∨ j ∈ after)
    (hbeforeSign :
      ∀ j ∈ before, raySignAt hp i j = sigma)
    (hafterSign :
      ∀ j ∈ after, raySignAt hp i j = !sigma)
    {thetaLeft thetaRight : ℝ}
    (hbeforeTheta :
      ∀ j ∈ before, rayThetaAt hp i j ≤ thetaLeft)
    (hafterTheta :
      ∀ j ∈ after, thetaRight ≤ rayThetaAt hp i j)
    (hthetaLeft0 : 0 ≤ thetaLeft)
    (hthetaRightPi : thetaRight < Real.pi)
    (hgap : thetaLeft < thetaRight) :
    StrictlyExposedAt p i := by
  let width : ℝ := thetaLeft + Real.pi - thetaRight
  have hwidth0 : 0 ≤ width := by
    dsimp [width]
    have hrightLe :
        thetaRight ≤ thetaLeft + Real.pi := by
      linarith [Real.pi_pos]
    linarith
  have hwidthPi : width < Real.pi := by
    dsimp [width]
    linarith
  apply strictlyExposedAt_of_common_signed_interval
    (p := p) (i := i)
    (a := thetaRight) (width := width)
    hwidth0 hwidthPi (!sigma)
  intro j hji
  let jo : OtherVertex i := ⟨j, hji⟩
  rcases hcover jo with hjBefore | hjAfter
  · refine ⟨rayRhoAt hp i jo,
      rayThetaAt hp i jo + Real.pi,
      rayRhoAt_pos hp i jo, ?_, ?_, ?_⟩
    · have hj0 := rayThetaAt_nonneg hp i jo
      linarith [hthetaRightPi]
    · have hjle := hbeforeTheta jo hjBefore
      dsimp [width]
      linarith
    · have hsign := hbeforeSign jo hjBefore
      rw [rayRepAt_eq hp i jo, hsign]
      rw [same_ray_after_pi_shift_to_common_sign]
  · refine ⟨rayRhoAt hp i jo,
      rayThetaAt hp i jo,
      rayRhoAt_pos hp i jo, ?_, ?_, ?_⟩
    · exact hafterTheta jo hjAfter
    · have hjPi := rayThetaAt_lt_pi hp i jo
      dsimp [width]
      linarith [hthetaLeft0]
    · have hsign := hafterSign jo hjAfter
      rw [rayRepAt_eq hp i jo, hsign]

/-- If every canonical ray has the same sign, the finite canonical angle range
already has width strictly below pi.  This is the wrap-transition case after
the only sign change occurs at the projective boundary. -/
theorem strictlyExposedAt_of_common_canonical_sign
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i : V}
    (sigma : Bool)
    (rays : List (OtherVertex i))
    (hrays : ∀ j : OtherVertex i, j ∈ rays)
    (hsign : ∀ j ∈ rays, raySignAt hp i j = sigma)
    (hne : rays ≠ [])
    (hsorted :
      rays.Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b)) :
    StrictlyExposedAt p i := by
  obtain ⟨first, rest, hr⟩ :
      ∃ first rest, rays = first :: rest := by
    cases h : rays with
    | nil => exact False.elim (hne h)
    | cons first rest => exact ⟨first, rest, h⟩
  have hpair :
      (first :: rest).Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
    simpa [hr] using hsorted
  let last : OtherVertex i :=
    (first :: rest).getLast (by simp)
  have hfirst0 := rayThetaAt_nonneg hp i first
  have hlastPi := rayThetaAt_lt_pi hp i last
  have hfirstLast :
      rayThetaAt hp i first ≤ rayThetaAt hp i last := by
    dsimp [last]
    exact hpair.rel_getLast (by simp)
  let width : ℝ :=
    rayThetaAt hp i last - rayThetaAt hp i first
  have hwidth0 : 0 ≤ width := by
    dsimp [width]
    linarith
  have hwidthPi : width < Real.pi := by
    dsimp [width]
    linarith
  apply strictlyExposedAt_of_common_signed_interval
    (p := p) (i := i)
    (a := rayThetaAt hp i first)
    (width := width)
    hwidth0 hwidthPi sigma
  intro j hji
  let jo : OtherVertex i := ⟨j, hji⟩
  have hjmem : jo ∈ first :: rest := by
    rw [← hr]
    exact hrays jo
  have hfirstLe :
      rayThetaAt hp i first ≤ rayThetaAt hp i jo := by
    rcases List.mem_cons.mp hjmem with hEq | htail
    · subst jo
      rfl
    · exact (List.pairwise_cons.mp hpair).1 jo htail
  have hjLast :
      rayThetaAt hp i jo ≤ rayThetaAt hp i last := by
    dsimp [last]
    exact hpair.rel_getLast hjmem
  refine ⟨rayRhoAt hp i jo,
    rayThetaAt hp i jo,
    rayRhoAt_pos hp i jo,
    hfirstLe, ?_, ?_⟩
  · dsimp [width]
    linarith
  · have hs : raySignAt hp i jo = sigma := by
      apply hsign jo
      simpa [hr] using hjmem
    rw [rayRepAt_eq hp i jo, hs]

#print axioms strictlyExposedAt_of_two_sign_blocks
#print axioms strictlyExposedAt_of_common_canonical_sign

end JSP000404Research
