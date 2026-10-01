import JSP000404Research.SignTransitionBudget
import Mathlib.Tactic

/-!
# Zero quotient blocks preserve the Boolean sign

ChangesOnlyOnPositive says that a sign change can occur only at a nonzero
quotient. Therefore an aligned quotient block consisting entirely of zeros
forces every sign in the corresponding sign block to equal the initial sign.

This tiny lemma is the combinatorial bridge needed to attach canonical-side
semantics to zero-quotient narrow arcs.
-/

namespace JSP000404Research

theorem changesOnlyOnPositive_all_zero_forces_all_signs_eq
    (a : Bool)
    (signs : List Bool)
    (qs : List ℕ)
    (hchanges : ChangesOnlyOnPositive a signs qs)
    (hzero : ∀ q ∈ qs, q = 0) :
    ∀ b ∈ signs, b = a := by
  induction signs generalizing a qs with
  | nil =>
      intro b hb
      simp at hb
  | cons b bs ih =>
      cases qs with
      | nil =>
          simp [ChangesOnlyOnPositive] at hchanges
      | cons q qs =>
          rcases hchanges with ⟨hstep,hrest⟩
          have hq0 : q = 0 :=
            hzero q (by simp)
          have hab : b = a := by
            by_contra hne
            exact hstep hne hq0
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hab
          · have htailZero : ∀ r ∈ qs, r = 0 := by
              intro r hr
              exact hzero r (by simp [hr])
            have htail := ih b qs hrest htailZero x hx
            exact htail.trans hab

theorem changesOnlyOnPositive_all_zero_last_eq
    (a : Bool)
    (signs : List Bool)
    (qs : List ℕ)
    (hchanges : ChangesOnlyOnPositive a signs qs)
    (hzero : ∀ q ∈ qs, q = 0) :
    boolLastFrom a signs = a := by
  induction signs generalizing a qs with
  | nil =>
      rfl
  | cons b bs ih =>
      cases qs with
      | nil =>
          simp [ChangesOnlyOnPositive] at hchanges
      | cons q qs =>
          rcases hchanges with ⟨hstep,hrest⟩
          have hq0 : q = 0 :=
            hzero q (by simp)
          have hab : b = a := by
            by_contra hne
            exact hstep hne hq0
          have htailZero : ∀ r ∈ qs, r = 0 := by
            intro r hr
            exact hzero r (by simp [hr])
          simp only [boolLastFrom]
          rw [ih b qs hrest htailZero, hab]

#print axioms changesOnlyOnPositive_all_zero_forces_all_signs_eq
#print axioms changesOnlyOnPositive_all_zero_last_eq

end JSP000404Research
