import JSP000404Research.SignTransitionBudget
import Mathlib.Tactic

/-!
# Zero quotient blocks freeze the lifted sign path

ChangesOnlyOnPositive says every Boolean sign change must be carried by a
positive quotient.  Therefore along a block of quotient zeros the lifted sign
is constant.

This elementary fact is the sign-theoretic input for arbitrary-cardinality
support-two clusters: once the two positive gaps are pinned around the sharp
ray, every middle gap is zero, so each ordinary side block has constant
canonical sign and the wrap step gives the expected flipped-sign relation.
-/

namespace JSP000404Research

theorem changesOnlyOnZero_forces_replicate
    (a : Bool)
    (signs : List Bool)
    (qs : List ℕ)
    (hchanges : ChangesOnlyOnPositive a signs qs)
    (hzero : ∀ q ∈ qs, q = 0) :
    signs = List.replicate qs.length a := by
  induction qs generalizing a signs with
  | nil =>
      cases signs with
      | nil =>
          rfl
      | cons b bs =>
          simp [ChangesOnlyOnPositive] at hchanges
  | cons q qs ih =>
      cases signs with
      | nil =>
          simp [ChangesOnlyOnPositive] at hchanges
      | cons b bs =>
          have hq0 : q = 0 := hzero q (by simp)
          subst q
          rcases hchanges with ⟨hstep, hrest⟩
          have hab : a = b := by
            by_contra hne
            exact (hstep hne) rfl
          subst b
          have htailZero :
              ∀ x ∈ qs, x = 0 := by
            intro x hx
            exact hzero x (by simp [hx])
          have htail := ih a bs hrest htailZero
          simp [htail]

/-- Pointwise form: every sign displayed along a zero quotient block equals
the entering sign. -/
theorem sign_eq_entry_of_zero_block
    (a : Bool)
    (signs : List Bool)
    (qs : List ℕ)
    (hchanges : ChangesOnlyOnPositive a signs qs)
    (hzero : ∀ q ∈ qs, q = 0)
    {b : Bool} (hb : b ∈ signs) :
    b = a := by
  rw [changesOnlyOnZero_forces_replicate
      a signs qs hchanges hzero] at hb
  simpa using (List.eq_of_mem_replicate hb)

/-- If a zero block terminates at a displayed final sign, that final sign is
also the entering sign. -/
theorem lastSign_eq_entry_of_zero_block
    (a : Bool)
    (signs : List Bool)
    (qs : List ℕ)
    (hchanges : ChangesOnlyOnPositive a signs qs)
    (hzero : ∀ q ∈ qs, q = 0) :
    boolLastFrom a signs = a := by
  rw [changesOnlyOnZero_forces_replicate
      a signs qs hchanges hzero]
  induction qs with
  | nil =>
      simp [boolLastFrom]
  | cons q qs ih =>
      simp [boolLastFrom]
      cases qs <;> simp [boolLastFrom]

#print axioms changesOnlyOnZero_forces_replicate
#print axioms sign_eq_entry_of_zero_block
#print axioms lastSign_eq_entry_of_zero_block

end JSP000404Research
