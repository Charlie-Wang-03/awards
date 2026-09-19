import JSP000404Research.CompensatedDeletion
import Mathlib.Tactic

/-!
# Minimal compensated-deletion induction shell

For the lower Sendov branch, deleting a top-level centre is followed by
perfect completion of the surviving rank-one circles at the same angle
parameter.  Abstractly, let

  W = sum_i 2^(exponent i)

be the current perfect weight and let post r be the completed weight after
deleting centre r.

To close the induction one does not need every deletion to be compensated,
nor any average-bonus statement.  It is enough to prove the dichotomy

  W <= bound
  or
  exists r, W <= post r.

If every completed (s-1)-centre object satisfies post r <= bound, either side
of the dichotomy gives W <= bound immediately.

This is the weakest induction outlet currently targeted for JSP-000404.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Minimal abstract deletion dichotomy. -/
theorem bound_of_direct_or_compensated_deletion
    {V : Type*} [Fintype V]
    (weight : V → ℕ)
    (post : V → ℕ)
    (bound : ℕ)
    (hdichotomy :
      (∑ i : V, weight i) ≤ bound ∨
        ∃ r : V, (∑ i : V, weight i) ≤ post r)
    (hind : ∀ r : V, post r ≤ bound) :
    (∑ i : V, weight i) ≤ bound := by
  rcases hdichotomy with hdirect | ⟨r, hcomp⟩
  · exact hdirect
  · exact hcomp.trans (hind r)

/-- Dyadic Sendov specialization. -/
theorem dyadic_bound_of_direct_or_compensated_deletion
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (post : V → ℕ)
    (bound : ℕ)
    (hdichotomy :
      (∑ i : V, 2 ^ exponent i) ≤ bound ∨
        ∃ r : V, (∑ i : V, 2 ^ exponent i) ≤ post r)
    (hind : ∀ r : V, post r ≤ bound) :
    (∑ i : V, 2 ^ exponent i) ≤ bound :=
  bound_of_direct_or_compensated_deletion
    (fun i => 2 ^ exponent i) post bound hdichotomy hind

/-- If the direct branch is not yet known, a single compensated deletion is
already sufficient. -/
theorem dyadic_bound_of_compensated_deletion
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (post : V → ℕ)
    (bound : ℕ)
    {r : V}
    (hcomp : (∑ i : V, 2 ^ exponent i) ≤ post r)
    (hind : post r ≤ bound) :
    (∑ i : V, 2 ^ exponent i) ≤ bound :=
  hcomp.trans hind

#print axioms bound_of_direct_or_compensated_deletion
#print axioms dyadic_bound_of_direct_or_compensated_deletion
#print axioms dyadic_bound_of_compensated_deletion

end JSP000404Research
