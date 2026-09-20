import JSP000404Research.BoolSignPath
import Mathlib.Tactic

/-!
# A short opposite-sign arc has one transition

Consider a lifted projective subarc, encoded by

* an initial sign `a`,
* the subsequent signs `signs`,
* the consecutive normalized gap lengths `gaps`.

The global angle cap says that every actual sign change consumes at least one
normalized unit.  If the total subarc length is strictly below two units, there
can therefore be at most one sign change.  If the final sign is the opposite
of the initial sign, antiperiodicity/parity forces at least one, hence exactly
one.

In the Sendov lower branch a wrap-triangle complement has length

  s <= 1 + delta < 3/2 < 2,

so this is the discrete core of the reduction from an arbitrary wrap triangle
to a unique adjacent critical sign-transition gap.
-/

namespace JSP000404Research

/-- Matching gap data in which every gap is nonnegative and every sign-changing
step has normalized length at least one. -/
def TransitionGapLowerBound : Bool → List Bool → List ℝ → Prop
  | _, [], [] => True
  | a, b :: bs, g :: gs =>
      0 ≤ g ∧ (a ≠ b → 1 ≤ g) ∧ TransitionGapLowerBound b bs gs
  | _, _, _ => False

/-- Each sign transition costs at least one unit of total gap length. -/
theorem transitionCount_le_gapSum
    (a : Bool) (signs : List Bool) (gaps : List ℝ)
    (h : TransitionGapLowerBound a signs gaps) :
    (boolTransitionCountFrom a signs : ℝ) ≤ gaps.sum := by
  induction signs generalizing a gaps with
  | nil =>
      cases gaps with
      | nil =>
          simp [boolTransitionCountFrom]
      | cons g gs =>
          simp [TransitionGapLowerBound] at h
  | cons b bs ih =>
      cases gaps with
      | nil =>
          simp [TransitionGapLowerBound] at h
      | cons g gs =>
          rcases h with ⟨hg0, hchange, hrest⟩
          have hi := ih b gs hrest
          by_cases hab : a = b
          · subst b
            simp [boolTransitionCountFrom]
            linarith
          · have hg1 : 1 ≤ g := hchange hab
            simp [boolTransitionCountFrom, hab]
            norm_num
            linarith

/-- Total normalized length below two permits at most one sign transition. -/
theorem transitionCount_le_one_of_gapSum_lt_two
    (a : Bool) (signs : List Bool) (gaps : List ℝ)
    (h : TransitionGapLowerBound a signs gaps)
    (hshort : gaps.sum < 2) :
    boolTransitionCountFrom a signs ≤ 1 := by
  have hreal := transitionCount_le_gapSum a signs gaps h
  have hlt : (boolTransitionCountFrom a signs : ℝ) < 2 :=
    hreal.trans_lt hshort
  exact_mod_cast (Nat.lt_of_cast_lt hlt : boolTransitionCountFrom a signs < 2)

/-- Opposite endpoint signs on such a short arc force exactly one transition. -/
theorem exactly_one_transition_of_short_opposite_arc
    (a : Bool) (signs : List Bool) (gaps : List ℝ)
    (h : TransitionGapLowerBound a signs gaps)
    (hlast : boolLastFrom a signs = !a)
    (hshort : gaps.sum < 2) :
    boolTransitionCountFrom a signs = 1 := by
  have hle :=
    transitionCount_le_one_of_gapSum_lt_two a signs gaps h hshort
  have hmod :=
    boolTransitionCountFrom_mod_two_eq_one_of_last_not a signs hlast
  omega

/-- Equal endpoint signs on a subarc of total normalized length below two
force zero transitions.  The transition count is at most one, while parity is
even. -/
theorem zero_transition_of_short_same_arc
    (a : Bool) (signs : List Bool) (gaps : List ℝ)
    (h : TransitionGapLowerBound a signs gaps)
    (hlast : boolLastFrom a signs = a)
    (hshort : gaps.sum < 2) :
    boolTransitionCountFrom a signs = 0 := by
  have hle :=
    transitionCount_le_one_of_gapSum_lt_two a signs gaps h hshort
  have hmod := boolTransitionCountFrom_mod_two a signs
  rw [hlast] at hmod
  simp at hmod
  omega

/-- Lower-branch specialization for a same-sign arc of length at most
`1+delta`. -/
theorem zero_transition_of_lower_branch_same_arc
    (a : Bool) (signs : List Bool) (gaps : List ℝ)
    {delta : ℝ}
    (hdelta : delta < (1 : ℝ) / 2)
    (h : TransitionGapLowerBound a signs gaps)
    (hlast : boolLastFrom a signs = a)
    (hlen : gaps.sum ≤ 1 + delta) :
    boolTransitionCountFrom a signs = 0 := by
  apply zero_transition_of_short_same_arc a signs gaps h hlast
  linarith

/-- Sendov lower-branch numerical specialization: a subarc of total length at
most `1+delta`, with `delta<1/2`, is certainly shorter than two units. -/
theorem exactly_one_transition_of_lower_branch_arc
    (a : Bool) (signs : List Bool) (gaps : List ℝ)
    {delta : ℝ}
    (hdelta : delta < (1 : ℝ) / 2)
    (h : TransitionGapLowerBound a signs gaps)
    (hlast : boolLastFrom a signs = !a)
    (hlen : gaps.sum ≤ 1 + delta) :
    boolTransitionCountFrom a signs = 1 := by
  apply exactly_one_transition_of_short_opposite_arc a signs gaps h hlast
  linarith

#print axioms transitionCount_le_gapSum
#print axioms transitionCount_le_one_of_gapSum_lt_two
#print axioms exactly_one_transition_of_short_opposite_arc
#print axioms zero_transition_of_short_same_arc
#print axioms zero_transition_of_lower_branch_same_arc
#print axioms exactly_one_transition_of_lower_branch_arc

end JSP000404Research
