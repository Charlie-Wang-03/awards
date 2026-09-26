import JSP000404Research.CanonicalSignGap
import JSP000404Research.UniqueTransitionGap
import Mathlib.Tactic

/-!
# Transition occurrence and uniqueness

This file introduces the transition-side analogue of SameSignQuotientOccurs.

A quotient value q occurs on a transition step when, in the aligned lifted sign
path, the two endpoint signs differ at a position carrying quotient q.

Two elementary facts are packaged:

* two distinct canonical rays with equal projective theta cannot have opposite
  signs under a strict Sendov angle cap; hence equal theta implies equal sign;
* if a lifted sign path has exactly one transition, then every transition
  occurrence is at the unique quotient selected by
  one_transition_positive_gap_decomposition.

These are the list/geometric interfaces needed to certify that the exact
witness unit quotient is the unique transition quotient in support-two.
-/

namespace JSP000404Research

/-- A quotient value occurs at an aligned sign-changing step. -/
def TransitionQuotientOccurs (q : ℕ) :
    Bool → List Bool → List ℕ → Prop
  | _, [], [] => False
  | a, b :: bs, r :: rs =>
      (r = q ∧ a ≠ b) ∨
        TransitionQuotientOccurs q b bs rs
  | _, _, _ => False

/-- Equal canonical projective parameters force equal canonical signs. -/
theorem raySignAt_eq_of_rayThetaAt_eq
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    (j k : OtherVertex i)
    (htheta :
      rayThetaAt hp i j = rayThetaAt hp i k) :
    raySignAt hp i j = raySignAt hp i k := by
  by_cases hjk : j = k
  · subst k
    rfl
  · by_contra hsign
    have horder :
        rayThetaAt hp i j ≤ rayThetaAt hp i k := by
      rw [htheta]
    have hone :=
      one_le_t_mul_gap_of_canonical_sign_ne
        hp hcap ht hlam i hjk horder hsign
    rw [← htheta] at hone
    norm_num at hone

/-- A transition occurrence survives prepending a same-sign aligned step. -/
theorem transitionQuotientOccurs_cons_same
    (q r : ℕ) (a : Bool)
    (signs : List Bool) (qs : List ℕ)
    (h : TransitionQuotientOccurs q a signs qs) :
    TransitionQuotientOccurs q a
      (a :: signs) (r :: qs) := by
  simp only [TransitionQuotientOccurs]
  exact Or.inr h

/-- In a two-block one-transition sign shape, the distinguished middle quotient
is the only quotient that can occur on a sign-changing step. -/
theorem transitionQuotientOccurs_two_blocks_iff
    (a : Bool)
    (pre post : List ℕ)
    (qe q : ℕ) :
    TransitionQuotientOccurs q a
      (List.replicate pre.length a ++
        List.replicate (post.length + 1) (!a))
      (pre ++ qe :: post)
      ↔
    qe = q := by
  induction pre generalizing a with
  | nil =>
      simp only [List.length_nil, List.replicate_zero,
        List.nil_append, List.replicate_succ,
        TransitionQuotientOccurs]
      constructor
      · intro h
        rcases h with hhead | htail
        · exact hhead.1
        · have hsame :
            ¬ TransitionQuotientOccurs q (!a)
              (List.replicate post.length (!a)) post := by
            induction post generalizing a with
            | nil =>
                simp [TransitionQuotientOccurs]
            | cons r rs ih =>
                simp only [List.length_cons, List.replicate_succ,
                  TransitionQuotientOccurs]
                intro hbad
                rcases hbad with hchange | hrest
                · exact hchange.2 rfl
                · exact ih (!a) hrest
          exact False.elim (hsame htail)
      · intro heq
        left
        refine ⟨heq, ?_⟩
        cases a <;> decide
  | cons r rs ih =>
      simp only [List.length_cons, List.replicate_succ,
        List.cons_append, TransitionQuotientOccurs]
      constructor
      · intro h
        rcases h with hhead | hrest
        · exact False.elim (hhead.2 rfl)
        · exact (ih a).1 hrest
      · intro heq
        right
        exact (ih a).2 heq

/-- Uniqueness outlet: if a concrete one-transition decomposition is known,
any transition occurrence of q identifies the distinguished quotient. -/
theorem unique_transition_quotient_eq_of_occurs
    (a : Bool) (signs : List Bool) (qs : List ℕ)
    (pre post : List ℕ) (qe q : ℕ)
    (hqs : qs = pre ++ qe :: post)
    (hsigns :
      signs =
        List.replicate pre.length a ++
          List.replicate (post.length + 1) (!a))
    (hocc :
      TransitionQuotientOccurs q a signs qs) :
    qe = q := by
  rw [hqs, hsigns] at hocc
  exact
    (transitionQuotientOccurs_two_blocks_iff
      a pre post qe q).1 hocc

#print axioms raySignAt_eq_of_rayThetaAt_eq
#print axioms transitionQuotientOccurs_two_blocks_iff
#print axioms unique_transition_quotient_eq_of_occurs

end JSP000404Research
