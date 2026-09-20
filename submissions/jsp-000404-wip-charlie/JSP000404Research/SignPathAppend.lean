import JSP000404Research.SignTransitionBudget
import Mathlib.Tactic

/-!
# Appending one step to a sign / quotient path

The actual projective ray cycle is easiest to prove in two pieces:

* consecutive sorted ray gaps;
* the final wrap gap.

This file supplies the pure list lemma that appends the wrap step after the
ordinary path has already been shown to change signs only on positive
quotients.
-/

namespace JSP000404Research

/-- Reading a nonempty appended singleton ends at that singleton value. -/
theorem boolLastFrom_append_singleton
    (a b : Bool) (xs : List Bool) :
    boolLastFrom a (xs ++ [b]) = b := by
  induction xs generalizing a with
  | nil => simp [boolLastFrom]
  | cons x xs ih =>
      simp only [List.cons_append, boolLastFrom]
      exact ih x

/-- Appending one aligned sign / quotient step preserves
ChangesOnlyOnPositive exactly when the new transition, if any, has positive
quotient. -/
theorem changesOnlyOnPositive_append_singleton
    (a b : Bool)
    (signs : List Bool) (qs : List ℕ) (q : ℕ)
    (h : ChangesOnlyOnPositive a signs qs)
    (hstep : boolLastFrom a signs ≠ b → q ≠ 0) :
    ChangesOnlyOnPositive a (signs ++ [b]) (qs ++ [q]) := by
  induction signs generalizing a qs with
  | nil =>
      cases qs with
      | nil =>
          simp only [List.nil_append]
          constructor
          · intro hab
            exact hstep (by simpa [boolLastFrom] using hab)
          · trivial
      | cons q0 qs =>
          simp [ChangesOnlyOnPositive] at h
  | cons x xs ih =>
      cases qs with
      | nil =>
          simp [ChangesOnlyOnPositive] at h
      | cons q0 qs =>
          rcases h with ⟨hhead, htail⟩
          simp only [List.cons_append, ChangesOnlyOnPositive]
          refine ⟨hhead, ?_⟩
          apply ih x qs
          · exact htail
          · intro hlast
            apply hstep
            simpa [boolLastFrom] using hlast

/-- Converse form: any valid appended path validates the final transition. -/
theorem appended_singleton_step_positive
    (a b : Bool)
    (signs : List Bool) (qs : List ℕ) (q : ℕ)
    (hlen : signs.length = qs.length)
    (h :
      ChangesOnlyOnPositive a (signs ++ [b]) (qs ++ [q])) :
    boolLastFrom a signs ≠ b → q ≠ 0 := by
  induction signs generalizing a qs with
  | nil =>
      cases qs with
      | nil =>
          simpa [ChangesOnlyOnPositive, boolLastFrom] using h
      | cons q0 qs =>
          simp at hlen
  | cons x xs ih =>
      cases qs with
      | nil =>
          simp at hlen
      | cons q0 qs =>
          simp at hlen
          simp only [List.cons_append, ChangesOnlyOnPositive] at h
          exact ih x qs hlen h.2

#print axioms boolLastFrom_append_singleton
#print axioms changesOnlyOnPositive_append_singleton
#print axioms appended_singleton_step_positive

end JSP000404Research
