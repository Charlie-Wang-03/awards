import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Lightweight deletion post-weight

The post-deletion dyadic weight is used both by pure arithmetic rigidity and
by the stronger deletion-bonus machinery.  Keep the definition in a minimal
module so arithmetic results do not inherit averaging / stability imports.
-/

namespace JSP000404Research

open scoped BigOperators

noncomputable def deletionPostWeight
    {V : Type*} [Fintype V]
    (after : V → V → ℕ)
    (r : V) : ℕ := by
  classical
  exact ∑ i ∈ Finset.univ.erase r, 2 ^ after r i

end JSP000404Research
