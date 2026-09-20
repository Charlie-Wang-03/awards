import JSP000404Research.TransitionSplitExposure
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic

/-!
# Common-signed interval data behind transition exposure

The strict-exposure theorems only return the existence of one supporting
vector.  Global turn packing needs the stronger data actually used in those
proofs: an interval containing every ray after a common-sign lift.

This file exposes that representation explicitly for both ordinary and wrap
transition cuts.
-/

namespace JSP000404Research

open Real

/-- Two opposite-sign canonical blocks can be lifted to one common sign on the
complement of the ordinary transition gap. -/
theorem commonSignedIntervalRepr_of_two_sign_blocks
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
    (hthetaRightPi : thetaRight < Real.pi) :
    ∀ j, j ≠ i →
      ∃ rho : ℝ, ∃ theta : ℝ,
        0 < rho ∧
        thetaRight ≤ theta ∧
        theta ≤ thetaLeft + Real.pi ∧
        p j - p i =
          rho • signedRayDirection (!sigma) theta := by
  intro j hji
  let jo : OtherVertex i := ⟨j, hji⟩
  rcases hcover jo with hjBefore | hjAfter
  · refine ⟨rayRhoAt hp i jo,
      rayThetaAt hp i jo + Real.pi,
      rayRhoAt_pos hp i jo, ?_, ?_, ?_⟩
    · have hj0 := rayThetaAt_nonneg hp i jo
      linarith
    · have hjle := hbeforeTheta jo hjBefore
      linarith
    · have hsign := hbeforeSign jo hjBefore
      rw [rayRepAt_eq hp i jo, hsign]
      exact same_ray_after_pi_shift_to_common_sign sigma _ 
  · refine ⟨rayRhoAt hp i jo,
      rayThetaAt hp i jo,
      rayRhoAt_pos hp i jo, ?_, ?_, ?_⟩
    · exact hafterTheta jo hjAfter
    · have hjPi := rayThetaAt_lt_pi hp i jo
      linarith
    · have hsign := hafterSign jo hjAfter
      rw [rayRepAt_eq hp i jo, hsign]

/-- A canonically sorted common-sign ray list already gives a common-signed
interval from its first to its last ray. -/
theorem commonSignedIntervalRepr_of_common_sign_cons
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i : V}
    (sigma : Bool)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hcover : ∀ j : OtherVertex i, j ∈ first :: rest)
    (hsign :
      ∀ j ∈ first :: rest, raySignAt hp i j = sigma)
    (hsorted :
      (first :: rest).Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b)) :
    let last := (first :: rest).getLast (by simp)
    ∀ j, j ≠ i →
      ∃ rho : ℝ, ∃ theta : ℝ,
        0 < rho ∧
        rayThetaAt hp i first ≤ theta ∧
        theta ≤ rayThetaAt hp i last ∧
        p j - p i =
          rho • signedRayDirection sigma theta := by
  let last := (first :: rest).getLast (by simp)
  intro j hji
  let jo : OtherVertex i := ⟨j, hji⟩
  have hjmem : jo ∈ first :: rest := hcover jo
  have hfirstLe :
      rayThetaAt hp i first ≤ rayThetaAt hp i jo := by
    rcases List.mem_cons.mp hjmem with hEq | htail
    · subst jo
      rfl
    · exact (List.pairwise_cons.mp hsorted).1 jo htail
  have hjLast :
      rayThetaAt hp i jo ≤ rayThetaAt hp i last := by
    dsimp [last]
    exact hsorted.rel_getLast hjmem
  refine ⟨rayRhoAt hp i jo,
    rayThetaAt hp i jo,
    rayRhoAt_pos hp i jo,
    hfirstLe, hjLast, ?_⟩
  have hs : raySignAt hp i jo = sigma :=
    hsign jo hjmem
  rw [rayRepAt_eq hp i jo, hs]

#print axioms commonSignedIntervalRepr_of_two_sign_blocks
#print axioms commonSignedIntervalRepr_of_common_sign_cons

end JSP000404Research
