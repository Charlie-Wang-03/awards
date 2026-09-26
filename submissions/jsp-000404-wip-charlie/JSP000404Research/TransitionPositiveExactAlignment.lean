import JSP000404Research.SignTransitionBudget
import Mathlib.Tactic

/-!
# Equality of transition count and positive support forces exact alignment

ChangesOnlyOnPositive gives only one implication:

  sign change -> positive quotient.

If the total number of sign changes equals the total number of positive
quotients, there can be no unused positive quotient.  Hence the converse holds
positionwise as well:

  positive quotient -> sign change.

This is the exact finite combinatorics needed in the support-three /
three-transition branch, where both totals equal three.
-/

namespace JSP000404Research

/-- Positionwise converse to ChangesOnlyOnPositive. -/
def PositiveOnlyOnTransition :
    Bool → List Bool → List ℕ → Prop
  | _, [], [] => True
  | a, b :: bs, q :: qs =>
      (q ≠ 0 → a ≠ b) ∧
        PositiveOnlyOnTransition b bs qs
  | _, _, _ => False

/-- If every transition is positive and the total transition count already
equals the positive support count, then every positive quotient is a
transition. -/
theorem positiveOnlyOnTransition_of_count_eq
    (a : Bool) (signs : List Bool) (qs : List ℕ)
    (hchanges : ChangesOnlyOnPositive a signs qs)
    (hcount :
      boolTransitionCountFrom a signs =
        listPositiveCount qs) :
    PositiveOnlyOnTransition a signs qs := by
  induction signs generalizing a qs with
  | nil =>
      cases qs with
      | nil =>
          trivial
      | cons q qs =>
          simp [ChangesOnlyOnPositive] at hchanges
  | cons b bs ih =>
      cases qs with
      | nil =>
          simp [ChangesOnlyOnPositive] at hchanges
      | cons q qs =>
          rcases hchanges with ⟨hstep, hrest⟩
          have htailLe :
              boolTransitionCountFrom b bs ≤
                listPositiveCount qs :=
            boolTransitionCount_le_listPositiveCount
              b bs qs hrest
          by_cases hab : a = b
          · subst b
            have hq0 : q = 0 := by
              by_contra hq
              simp [boolTransitionCountFrom,
                listPositiveCount, hq] at hcount
              omega
            have htailEq :
                boolTransitionCountFrom a bs =
                  listPositiveCount qs := by
              simpa [boolTransitionCountFrom,
                listPositiveCount, hq0] using hcount
            constructor
            · intro hbad
              exact False.elim (hbad hq0)
            · exact ih a qs hrest htailEq
          · have hq : q ≠ 0 := hstep hab
            have htailEq :
                boolTransitionCountFrom b bs =
                  listPositiveCount qs := by
              simp [boolTransitionCountFrom,
                listPositiveCount, hab, hq] at hcount
              omega
            constructor
            · intro _
              exact hab
            · exact ih b qs hrest htailEq

/-- Three-transition/support-three specialization. -/
theorem support_three_three_transitions_all_positive_are_transitions
    (a : Bool) (signs : List Bool) (qs : List ℕ)
    (hchanges : ChangesOnlyOnPositive a signs qs)
    (htrans : boolTransitionCountFrom a signs = 3)
    (hsupport : listPositiveCount qs = 3) :
    PositiveOnlyOnTransition a signs qs := by
  apply positiveOnlyOnTransition_of_count_eq
      a signs qs hchanges
  omega

/-- Therefore in the three-transition/support-three case the positive quotient
positions and the transition positions coincide exactly. -/
theorem support_three_three_transitions_exact_alignment
    (a : Bool) (signs : List Bool) (qs : List ℕ)
    (hchanges : ChangesOnlyOnPositive a signs qs)
    (htrans : boolTransitionCountFrom a signs = 3)
    (hsupport : listPositiveCount qs = 3) :
    ChangesOnlyOnPositive a signs qs ∧
      PositiveOnlyOnTransition a signs qs := by
  exact ⟨hchanges,
    support_three_three_transitions_all_positive_are_transitions
      a signs qs hchanges htrans hsupport⟩

#print axioms positiveOnlyOnTransition_of_count_eq
#print axioms support_three_three_transitions_all_positive_are_transitions
#print axioms support_three_three_transitions_exact_alignment

end JSP000404Research
