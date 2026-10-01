import JSP000404Research.CanonicalFourPointSideTable
import Mathlib.Tactic

/-!
# Support-two occupancy of the canonical four-point order

Among four canonically ordered points a<b<c<d, if at least three satisfy a
predicate P, then at least one of the two middle ranks b,c satisfies P.  More
precisely, either both middle ranks satisfy P, or both extremes do and exactly
one middle rank does.

This is a small but useful finite reduction for the Q/T/T/T branch where P is
"second-layer support-two".
-/

namespace JSP000404Research

theorem three_of_four_predicate_hits_middle
    {V : Type*}
    (P : V → Prop)
    {a b c d : V}
    (hthree :
      (P a ∧ P b ∧ P c) ∨
      (P a ∧ P b ∧ P d) ∨
      (P a ∧ P c ∧ P d) ∨
      (P b ∧ P c ∧ P d)) :
    P b ∨ P c := by
  rcases hthree with h | h | h | h
  · exact Or.inl h.2.1
  · exact Or.inl h.2.1
  · exact Or.inr h.2.1
  · exact Or.inl h.1

theorem three_of_four_predicate_middle_structure
    {V : Type*}
    (P : V → Prop)
    {a b c d : V}
    (hthree :
      (P a ∧ P b ∧ P c) ∨
      (P a ∧ P b ∧ P d) ∨
      (P a ∧ P c ∧ P d) ∨
      (P b ∧ P c ∧ P d)) :
    (P b ∧ P c) ∨
    (P a ∧ P d ∧ (P b ∨ P c)) := by
  rcases hthree with h | h | h | h
  · exact Or.inl ⟨h.2.1,h.2.2⟩
  · exact Or.inr ⟨h.1,h.2.2,Or.inl h.2.1⟩
  · exact Or.inr ⟨h.1,h.2.2,Or.inr h.2.1⟩
  · exact Or.inl ⟨h.1,h.2.1⟩

/-- If both canonical middle ranks are marked support-two, a same-side pair at
the lower middle rank b is forced to be the upper pair {c,d}. -/
theorem lower_middle_sameSide_pair_forced
    {V : Type*} {p : V → Plane}
    {a b c d : V}
    (hab : CanonicalPointLt p a b)
    (hbc : CanonicalPointLt p b c)
    (hcd : CanonicalPointLt p c d)
    {x y : V}
    (hxy :
      (x = a ∧ y = c) ∨
      (x = a ∧ y = d) ∨
      (x = c ∧ y = d))
    (hsame : CanonicalSameSide p b x y) :
    x = c ∧ y = d := by
  have huniq := canonical_middle_b_sameSide_unique hab hbc hcd
  rcases hxy with h | h | h
  · rcases h with ⟨rfl,rfl⟩
    exact False.elim (huniq.1 hsame)
  · rcases h with ⟨rfl,rfl⟩
    exact False.elim (huniq.2.1 hsame)
  · exact h

/-- At the upper middle rank c, a same-side pair is forced to be the lower
pair {a,b}. -/
theorem upper_middle_sameSide_pair_forced
    {V : Type*} {p : V → Plane}
    {a b c d : V}
    (hab : CanonicalPointLt p a b)
    (hbc : CanonicalPointLt p b c)
    (hcd : CanonicalPointLt p c d)
    {x y : V}
    (hxy :
      (x = a ∧ y = b) ∨
      (x = a ∧ y = d) ∨
      (x = b ∧ y = d))
    (hsame : CanonicalSameSide p c x y) :
    x = a ∧ y = b := by
  have huniq := canonical_middle_c_sameSide_unique hab hbc hcd
  rcases hxy with h | h | h
  · exact h
  · rcases h with ⟨rfl,rfl⟩
    exact False.elim (huniq.2.1 hsame)
  · rcases h with ⟨rfl,rfl⟩
    exact False.elim (huniq.2.2 hsame)

#print axioms three_of_four_predicate_middle_structure
#print axioms lower_middle_sameSide_pair_forced
#print axioms upper_middle_sameSide_pair_forced

end JSP000404Research
