import JSP000404Research.BoolSignPath
import Mathlib.Tactic

/-!
# Sign shape of a middle-hidden three-transition cycle

A six-point support-three middle-hidden quotient pattern has the cyclic form

  [qFirst, 0, qHidden, 0, qLast].

When the corresponding lifted sign path uses three transitions, the two zero
quotient positions cannot change sign.  Hence the only antiperiodic Boolean
shape is

  a, !a, !a, a, a, !a.

The module is deliberately independent of the older
`SignTransitionBudget` file, whose Lean-4.34 compatibility repair is tracked
separately.
-/

namespace JSP000404Research

/-- Five-step antiperiodic path with exactly three transitions and no changes
on the second and fourth steps has the alternating two-pair shape. -/
theorem middle_hidden_three_transition_sign_shape
    (a r b c d : Bool)
    (htrans :
      boolTransitionCountFrom a [r,b,c,d,!a] = 3)
    (hrb : r = b)
    (hcd : c = d) :
    r = !a ∧ b = !a ∧ c = a ∧ d = a := by
  subst b
  subst d
  cases a <;> cases r <;> cases c <;>
    simp_all [boolTransitionCountFrom]

/-- Concrete five-step "changes only on positive" condition, specialized to
the middle-hidden quotient pattern. -/
def MiddleHiddenChangesOnlyOnPositive
    (a r b c d : Bool)
    (qFirst qHidden qLast : ℕ) : Prop :=
  (a ≠ r → qFirst ≠ 0) ∧
  (r ≠ b → (0 : ℕ) ≠ 0) ∧
  (b ≠ c → qHidden ≠ 0) ∧
  (c ≠ d → (0 : ℕ) ≠ 0) ∧
  (d ≠ !a → qLast ≠ 0)

/-- The specialized positivity condition forces the same sign shape. -/
theorem middle_hidden_sign_shape_of_local_changes
    (a r b c d : Bool)
    (qFirst qHidden qLast : ℕ)
    (hchanges :
      MiddleHiddenChangesOnlyOnPositive
        a r b c d qFirst qHidden qLast)
    (htrans :
      boolTransitionCountFrom a [r,b,c,d,!a] = 3) :
    r = !a ∧ b = !a ∧ c = a ∧ d = a := by
  have hrb : r = b := by
    by_contra hne
    exact (hchanges.2.1 hne) rfl
  have hcd : c = d := by
    by_contra hne
    exact (hchanges.2.2.2.1 hne) rfl
  exact middle_hidden_three_transition_sign_shape
    a r b c d htrans hrb hcd

/-- The two zero-gap pairs have equal signs internally and opposite signs
across the hidden positive slot. -/
theorem middle_hidden_pair_sign_relations
    (a r b c d : Bool)
    (qFirst qHidden qLast : ℕ)
    (hchanges :
      MiddleHiddenChangesOnlyOnPositive
        a r b c d qFirst qHidden qLast)
    (htrans :
      boolTransitionCountFrom a [r,b,c,d,!a] = 3) :
    r = b ∧ c = d ∧ r ≠ c := by
  obtain ⟨hr,hb,hc,hd⟩ :=
    middle_hidden_sign_shape_of_local_changes
      a r b c d qFirst qHidden qLast hchanges htrans
  constructor
  · exact hr.trans hb.symm
  · constructor
    · exact hc.trans hd.symm
    · rw [hr,hc]
      cases a <;> decide

#print axioms middle_hidden_three_transition_sign_shape
#print axioms middle_hidden_sign_shape_of_local_changes
#print axioms middle_hidden_pair_sign_relations

end JSP000404Research
