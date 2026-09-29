import JSP000404Research.SignTransitionBudget
import Mathlib.Tactic

/-!
# Sign shape of a middle-hidden three-transition cycle

A six-point support-three middle-hidden quotient pattern has the cyclic form

  [qFirst, 0, qHidden, 0, qLast].

When the corresponding lifted sign path uses three transitions, the two zero
quotient positions cannot change sign.  Since the lifted endpoint is the
complement of the starting sign, the only possible Boolean shape is

  a, !a, !a, a, a, !a.

Thus the two zero-gap matching edges form two same-sign pairs, and the two
pairs carry opposite signs.

This is pure finite combinatorics; the geometric rotation bridge is kept
separate.
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

/-- The same conclusion follows directly from the
`ChangesOnlyOnPositive` predicate aligned with the middle-hidden quotient
pattern.  No assumptions on the three positive quotient values beyond the
transition count are needed. -/
theorem middle_hidden_sign_shape_of_changesOnlyOnPositive
    (a r b c d : Bool)
    (qFirst qHidden qLast : ℕ)
    (hchanges :
      ChangesOnlyOnPositive a
        [r,b,c,d,!a]
        [qFirst,0,qHidden,0,qLast])
    (htrans :
      boolTransitionCountFrom a [r,b,c,d,!a] = 3) :
    r = !a ∧ b = !a ∧ c = a ∧ d = a := by
  have hrb : r = b := by
    by_contra hne
    have hzero : (0 : ℕ) ≠ 0 := by
      simpa [ChangesOnlyOnPositive] using hchanges.2.1 hne
    exact hzero rfl
  have hcd : c = d := by
    by_contra hne
    have hzero : (0 : ℕ) ≠ 0 := by
      simpa [ChangesOnlyOnPositive] using hchanges.2.2.2.1 hne
    exact hzero rfl
  exact middle_hidden_three_transition_sign_shape
    a r b c d htrans hrb hcd

/-- In particular, the two zero-gap pairs have equal signs internally and
opposite signs across the hidden positive gap. -/
theorem middle_hidden_pair_sign_relations
    (a r b c d : Bool)
    (qFirst qHidden qLast : ℕ)
    (hchanges :
      ChangesOnlyOnPositive a
        [r,b,c,d,!a]
        [qFirst,0,qHidden,0,qLast])
    (htrans :
      boolTransitionCountFrom a [r,b,c,d,!a] = 3) :
    r = b ∧ c = d ∧ r ≠ c := by
  obtain ⟨hr, hb, hc, hd⟩ :=
    middle_hidden_sign_shape_of_changesOnlyOnPositive
      a r b c d qFirst qHidden qLast hchanges htrans
  constructor
  · exact hr.trans hb.symm
  · constructor
    · exact hc.trans hd.symm
    · rw [hr, hc]
      cases a <;> decide

#print axioms middle_hidden_three_transition_sign_shape
#print axioms middle_hidden_sign_shape_of_changesOnlyOnPositive
#print axioms middle_hidden_pair_sign_relations

end JSP000404Research
