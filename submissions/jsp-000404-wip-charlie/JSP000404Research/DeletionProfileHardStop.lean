import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Hard stop for a profile-only compensated-deletion principle

This file records a tiny exact dyadic weight profile showing that compensated
deletion cannot follow from the old exponent multiset and the number of
survivors alone.

Old exponents on four centres:

  (0,1,1,1)

have total dyadic weight 7.

If every one-point deletion leaves three exponent-one survivors, every
post-deletion weight is only 6.  Hence no deletion is compensated.

This is deliberately an abstract profile certificate only.  It does NOT claim
that the profile is geometrically realizable by a JSP-000404 configuration.
A separate numerical search has produced a robust planar candidate, but that
geometric realization requires independent analytic certification before it
may be promoted to a theorem.
-/

namespace JSP000404Research

open scoped BigOperators

def deletionHardStopOldExponent : Fin 4 → ℕ :=
  ![0, 1, 1, 1]

def deletionHardStopAfterExponent (_r : Fin 4) : Fin 3 → ℕ :=
  ![1, 1, 1]

def deletionHardStopOldWeight : ℕ :=
  ∑ i : Fin 4, 2 ^ deletionHardStopOldExponent i

def deletionHardStopPostWeight (r : Fin 4) : ℕ :=
  ∑ j : Fin 3, 2 ^ deletionHardStopAfterExponent r j

theorem deletionHardStopOldWeight_eq :
    deletionHardStopOldWeight = 7 := by
  native_decide

theorem deletionHardStopPostWeight_eq (r : Fin 4) :
    deletionHardStopPostWeight r = 6 := by
  fin_cases r <;> native_decide

/-- No deletion in this exact abstract profile can compensate the original
dyadic mass. -/
theorem deletionHardStop_no_compensated_deletion :
    ¬ ∃ r : Fin 4,
      deletionHardStopOldWeight ≤ deletionHardStopPostWeight r := by
  intro h
  obtain ⟨r, hr⟩ := h
  rw [deletionHardStopOldWeight_eq,
      deletionHardStopPostWeight_eq r] at hr
  omega

#print axioms deletionHardStopOldWeight_eq
#print axioms deletionHardStopPostWeight_eq
#print axioms deletionHardStop_no_compensated_deletion

end JSP000404Research
