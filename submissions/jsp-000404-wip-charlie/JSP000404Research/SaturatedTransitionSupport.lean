import JSP000404Research.SignTransitionBudget
import Mathlib.Tactic

/-!
# Saturated transition support

`ChangesOnlyOnPositive` says that every sign change is carried by a positive
quotient.  If the number of sign changes reaches the full positive support,
then no positive quotient can be unused: sign changes occur exactly at the
positive positions.

This is the finite combinatorial upgrade needed for non-exposed
support-three centres, where both counts are exactly three.
-/

namespace JSP000404Research

def ChangesExactlyOnPositive : Bool → List Bool → List ℕ → Prop
  | _, [], [] => True
  | a, b :: bs, q :: qs =>
      ((a ≠ b) ↔ q ≠ 0) ∧
        ChangesExactlyOnPositive b bs qs
  | _, _, _ => False

theorem changesExactlyOnPositive_of_saturated_count
    (a : Bool) (signs : List Bool) (qs : List ℕ)
    (hchanges : ChangesOnlyOnPositive a signs qs)
    (hsat :
      boolTransitionCountFrom a signs =
        listPositiveCount qs) :
    ChangesExactlyOnPositive a signs qs := by
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
          rcases hchanges with ⟨hstep,hrest⟩
          have htail :
              boolTransitionCountFrom b bs ≤
                listPositiveCount qs :=
            boolTransitionCount_le_listPositiveCount
              b bs qs hrest
          by_cases hab : a = b
          · subst b
            by_cases hq : q = 0
            · constructor
              · simp [hq]
              · apply ih a qs hrest
                simp [boolTransitionCountFrom,
                  listPositiveCount, hq] at hsat
                exact hsat
            · exfalso
              simp [boolTransitionCountFrom,
                listPositiveCount, hq] at hsat
              omega
          · have hq : q ≠ 0 := hstep hab
            constructor
            · exact ⟨hab,hq⟩
            · apply ih b qs hrest
              simp [boolTransitionCountFrom,
                listPositiveCount, hab, hq] at hsat
              exact hsat

theorem positive_step_changes_of_saturated_count
    (a b : Bool)
    (bs : List Bool)
    (q : ℕ) (qs : List ℕ)
    (hchanges :
      ChangesOnlyOnPositive a (b :: bs) (q :: qs))
    (hsat :
      boolTransitionCountFrom a (b :: bs) =
        listPositiveCount (q :: qs))
    (hq : q ≠ 0) :
    a ≠ b := by
  have hexact :=
    changesExactlyOnPositive_of_saturated_count
      a (b :: bs) (q :: qs) hchanges hsat
  exact hexact.1.mpr hq

#print axioms ChangesExactlyOnPositive
#print axioms changesExactlyOnPositive_of_saturated_count
#print axioms positive_step_changes_of_saturated_count

end JSP000404Research
