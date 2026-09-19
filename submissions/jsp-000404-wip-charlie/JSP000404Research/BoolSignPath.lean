import Mathlib.Tactic

/-!
# Transition parity on an antiperiodic Boolean sign path

A lifted traversal of the projective direction circle begins with some sign
sigma and ends with !sigma.  Therefore the number of sign changes along the
lift is odd.

This file packages the elementary list combinatorics independently of the
geometry.  In particular, if at most two gaps are allowed to carry a sign
change, an antiperiodic path has exactly one transition.
-/

namespace JSP000404Research

/-- Number of adjacent sign changes when starting from sign a and reading a
list of subsequent signs. -/
def boolTransitionCountFrom (a : Bool) : List Bool → ℕ
  | [] => 0
  | b :: xs =>
      (if a = b then 0 else 1) + boolTransitionCountFrom b xs

/-- Last sign reached from a after reading a list; for the empty list it is a. -/
def boolLastFrom (a : Bool) : List Bool → Bool
  | [] => a
  | b :: xs => boolLastFrom b xs

/-- Transition parity records whether the final sign equals the initial sign. -/
theorem boolTransitionCountFrom_mod_two
    (a : Bool) (xs : List Bool) :
    boolTransitionCountFrom a xs % 2 =
      if a = boolLastFrom a xs then 0 else 1 := by
  induction xs generalizing a with
  | nil =>
      simp [boolTransitionCountFrom, boolLastFrom]
  | cons b xs ih =>
      cases a <;> cases b <;>
        simp [boolTransitionCountFrom, boolLastFrom, ih, Nat.add_mod]
      all_goals
        generalize hlast : boolLastFrom true xs = z
        cases z <;>
          simp [ih, hlast, Nat.add_mod]
      all_goals
        generalize hlast : boolLastFrom false xs = z
        cases z <;>
          simp [ih, hlast, Nat.add_mod]

/-- Antiperiodic endpoints force an odd transition count. -/
theorem boolTransitionCountFrom_mod_two_eq_one_of_last_not
    (a : Bool) (xs : List Bool)
    (hlast : boolLastFrom a xs = !a) :
    boolTransitionCountFrom a xs % 2 = 1 := by
  rw [boolTransitionCountFrom_mod_two, hlast]
  cases a <;> simp

/-- If an antiperiodic sign path has at most two transitions, it has exactly
one. -/
theorem boolTransitionCountFrom_eq_one_of_last_not_of_le_two
    (a : Bool) (xs : List Bool)
    (hlast : boolLastFrom a xs = !a)
    (hle : boolTransitionCountFrom a xs ≤ 2) :
    boolTransitionCountFrom a xs = 1 := by
  have hmod :=
    boolTransitionCountFrom_mod_two_eq_one_of_last_not a xs hlast
  omega

#print axioms boolTransitionCountFrom_mod_two
#print axioms boolTransitionCountFrom_mod_two_eq_one_of_last_not
#print axioms boolTransitionCountFrom_eq_one_of_last_not_of_le_two

end JSP000404Research
