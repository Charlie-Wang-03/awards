import Mathlib.Tactic

/-!
# Three-step consequences of an exact transition decomposition

For a three-gap projective cycle, an exact decomposition

  [q0,q1,q2] = pre ++ qe :: post

together with the two-block lifted sign shape says that qe is the unique
sign-transition position.  Consequently any coordinate whose quotient value
is different from qe is a no-transition step.

The three conclusions correspond to the two ordinary gaps and the final wrap
gap.
-/

namespace JSP000404Research

theorem three_step_same_sign_of_ne_transition_value
    (s0 s1 s2 : Bool)
    (q0 q1 q2 qe : ℕ)
    (pre post : List ℕ)
    (hq :
      [q0,q1,q2] = pre ++ qe :: post)
    (hs :
      [s1,s2,!s0] =
        List.replicate pre.length s0 ++
          List.replicate (post.length + 1) (!s0)) :
    (q0 ≠ qe → s1 = s0) ∧
      (q1 ≠ qe → s2 = s1) ∧
      (q2 ≠ qe → s2 = !s0) := by
  have hlen :
      pre.length + 1 + post.length = 3 := by
    have h := congrArg List.length hq
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm
  have hpreLe : pre.length ≤ 2 := by omega
  interval_cases hpre : pre.length
  · have hpreNil : pre = [] := List.length_eq_zero.mp hpre
    subst pre
    have hpostLen : post.length = 2 := by omega
    obtain ⟨u,v,hpost⟩ := List.length_eq_two.mp hpostLen
    subst post
    simp at hq hs ⊢
    aesop
  · have hpreLen : pre.length = 1 := hpre
    obtain ⟨u,hpreList⟩ := List.length_eq_one.mp hpreLen
    subst pre
    have hpostLen : post.length = 1 := by omega
    obtain ⟨v,hpostList⟩ := List.length_eq_one.mp hpostLen
    subst post
    simp at hq hs ⊢
    aesop
  · have hpreLen : pre.length = 2 := hpre
    obtain ⟨u,v,hpreList⟩ := List.length_eq_two.mp hpreLen
    subst pre
    have hpostLen : post.length = 0 := by omega
    have hpostNil : post = [] := List.length_eq_zero.mp hpostLen
    subst post
    simp at hq hs ⊢
    aesop

#print axioms three_step_same_sign_of_ne_transition_value

end JSP000404Research
