import JSP000404Research.BoolSignShape
import Mathlib.Tactic

/-!
# Locating the unique sign transition in the quotient gaps

The previous modules show that an antiperiodic sign path with quotient support
at most two has exactly one sign transition.  For geometry we also need to
locate that transition in the aligned quotient list.

This file proves a stronger decomposition.  If a sign path changes exactly
once and every sign change is allowed only on a positive quotient, then the
aligned quotient list splits as

  pre ++ q :: post

with q != 0, while the sign list has the corresponding two-block form

  replicate |pre| a ++ replicate (|post|+1) (!a).

Thus the unique transition is carried by a genuinely positive quotient gap.
In Sendov normalization that gap has angular width at least one cap unit.
-/

namespace JSP000404Research

/-- Alignment predicate forces equal list lengths. -/
theorem changesOnlyOnPositive_length
    (a : Bool) (signs : List Bool) (qs : List ℕ)
    (h : ChangesOnlyOnPositive a signs qs) :
    signs.length = qs.length := by
  induction signs generalizing a qs with
  | nil =>
      cases qs <;> simp [ChangesOnlyOnPositive] at h ⊢
  | cons b bs ih =>
      cases qs with
      | nil =>
          simp [ChangesOnlyOnPositive] at h
      | cons q qs =>
          rcases h with ⟨_, hrest⟩
          simp [ih b qs hrest]

/-- Exact one-transition decomposition aligned with a positive quotient gap. -/
theorem one_transition_positive_gap_decomposition
    (a : Bool) (signs : List Bool) (qs : List ℕ)
    (hchanges : ChangesOnlyOnPositive a signs qs)
    (htrans : boolTransitionCountFrom a signs = 1) :
    ∃ pre post : List ℕ, ∃ q : ℕ,
      q ≠ 0 ∧
      qs = pre ++ q :: post ∧
      signs =
        List.replicate pre.length a ++
          List.replicate (post.length + 1) (!a) := by
  induction signs generalizing a qs with
  | nil =>
      simp [boolTransitionCountFrom] at htrans
  | cons b bs ih =>
      cases qs with
      | nil =>
          simp [ChangesOnlyOnPositive] at hchanges
      | cons q qs =>
          rcases hchanges with ⟨hstep, hrest⟩
          by_cases hab : a = b
          · subst b
            simp only [boolTransitionCountFrom, if_pos rfl, zero_add] at htrans
            obtain ⟨pre, post, q0, hq0, hqs, hsigns⟩ :=
              ih a qs hrest htrans
            refine ⟨q :: pre, post, q0, hq0, ?_, ?_⟩
            · simp [hqs]
            · rw [hsigns]
              simp [List.replicate_succ, List.cons_append]
          · have hb : b = !a := bool_eq_not_of_ne hab
            have hq : q ≠ 0 := hstep hab
            have hrestZero :
                boolTransitionCountFrom b bs = 0 := by
              simp only [boolTransitionCountFrom, hab, if_false] at htrans
              omega
            have hall :
                ∀ x ∈ bs, x = b :=
              (boolTransitionCountFrom_eq_zero_iff b bs).1 hrestZero
            have hbs :
                bs = List.replicate bs.length b :=
              list_eq_replicate_length_of_forall_eq b bs hall
            have hlen : bs.length = qs.length :=
              changesOnlyOnPositive_length b bs qs hrest
            refine ⟨[], qs, q, hq, by simp, ?_⟩
            subst b
            rw [hbs]
            simp [hlen, List.replicate_succ]

/-- Antiperiodicity and quotient support <=2 locate a positive unique
transition gap and produce the matching two-block sign decomposition. -/
theorem antiperiodic_positive_transition_gap_of_support_le_two
    (a : Bool) (signs : List Bool) (qs : List ℕ)
    (hchanges : ChangesOnlyOnPositive a signs qs)
    (hlast : boolLastFrom a signs = !a)
    (hsupport : listPositiveCount qs ≤ 2) :
    ∃ pre post : List ℕ, ∃ q : ℕ,
      q ≠ 0 ∧
      qs = pre ++ q :: post ∧
      signs =
        List.replicate pre.length a ++
          List.replicate (post.length + 1) (!a) := by
  have htrans :=
    one_sign_transition_of_support_le_two
      a signs qs hchanges hlast hsupport
  exact one_transition_positive_gap_decomposition
    a signs qs hchanges htrans

#print axioms changesOnlyOnPositive_length
#print axioms one_transition_positive_gap_decomposition
#print axioms antiperiodic_positive_transition_gap_of_support_le_two

end JSP000404Research
