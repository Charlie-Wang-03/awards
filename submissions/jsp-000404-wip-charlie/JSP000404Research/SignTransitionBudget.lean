import JSP000404Research.BoolSignPath
import Mathlib.Tactic

/-!
# Positive quotient gaps budget sign transitions

For a lifted projective-ray path, a sign change can occur only across a gap
whose quotient is positive. This file isolates that finite combinatorics.

The signs are read from an initial sign a through a list of subsequent signs;
the quotient list records the corresponding consecutive gaps. The recursive
predicate ChangesOnlyOnPositive says every sign-changing step has nonzero
quotient.

Then the number of sign transitions is at most the number of positive quotient
gaps. Combined with projective antiperiodicity, support at most two forces
exactly one sign transition.
-/

namespace JSP000404Research

/-- Number of positive entries of a quotient list. -/
def listPositiveCount : List ℕ → ℕ
  | [] => 0
  | q :: qs => (if q = 0 then 0 else 1) + listPositiveCount qs

/-- Stepwise condition that every sign change is carried by a positive
quotient gap. Mismatched list lengths are rejected. -/
def ChangesOnlyOnPositive : Bool → List Bool → List ℕ → Prop
  | _, [], [] => True
  | a, b :: bs, q :: qs =>
      (a ≠ b → q ≠ 0) ∧ ChangesOnlyOnPositive b bs qs
  | _, _, _ => False

/-- Sign-transition count is bounded by positive quotient support. -/
theorem boolTransitionCount_le_listPositiveCount
    (a : Bool) (signs : List Bool) (qs : List ℕ)
    (h : ChangesOnlyOnPositive a signs qs) :
    boolTransitionCountFrom a signs ≤ listPositiveCount qs := by
  induction signs generalizing a qs with
  | nil =>
      cases qs with
      | nil =>
          simp [boolTransitionCountFrom, listPositiveCount]
      | cons q qs =>
          simp [ChangesOnlyOnPositive] at h
  | cons b bs ih =>
      cases qs with
      | nil =>
          simp [ChangesOnlyOnPositive] at h
      | cons q qs =>
          rcases h with ⟨hstep, hrest⟩
          have hi := ih b qs hrest
          by_cases hab : a = b
          · subst b
            by_cases hq : q = 0
            · simp [boolTransitionCountFrom, listPositiveCount, hq]
              exact hi
            · simp [boolTransitionCountFrom, listPositiveCount, hq]
              omega
          · have hq : q ≠ 0 := hstep hab
            simp [boolTransitionCountFrom, listPositiveCount, hab, hq]
            omega

/-- Antiperiodicity plus at most two positive quotient gaps forces exactly one
sign transition. -/
theorem one_sign_transition_of_support_le_two
    (a : Bool) (signs : List Bool) (qs : List ℕ)
    (hchanges : ChangesOnlyOnPositive a signs qs)
    (hlast : boolLastFrom a signs = !a)
    (hsupport : listPositiveCount qs ≤ 2) :
    boolTransitionCountFrom a signs = 1 := by
  have htrans :
      boolTransitionCountFrom a signs ≤ 2 :=
    (boolTransitionCount_le_listPositiveCount a signs qs hchanges).trans hsupport
  exact boolTransitionCountFrom_eq_one_of_last_not_of_le_two
    a signs hlast htrans

#print axioms boolTransitionCount_le_listPositiveCount
#print axioms one_sign_transition_of_support_le_two

end JSP000404Research
