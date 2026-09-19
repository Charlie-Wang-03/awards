import JSP000404Research.ClusterCoverArithmetic
import Mathlib.Tactic

/-!
# Convex-hull turning-slot budget

For a counterclockwise convex polygon the exterior turning angles sum to
2*pi.  After normalization by the Sendov unit

  lambda = pi / (n+delta),

their total normalized width is

  2 * (n+delta).

In the lower branch delta < 1/2 this is strictly below 2n+1.  Therefore the
sum of the natural floors of all normalized hull turns is at most 2n.

The intended phase-obstruction argument assigns each bad phase component to a
unit slot in one hull normal cone.  Once the geometric injection is proved,
the theorem below supplies the global obstruction-count bound m <= 2n.

This module contains only the finite real/integer arithmetic; convex-hull
geometry is deliberately not assumed here.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Floors of normalized exterior turns sum to at most 2n in the lower
delta branch. -/
theorem hull_turn_floor_budget
    {I : Type*} [Fintype I]
    (turn : I → ℝ) (n : ℕ) (delta : ℝ)
    (hturn0 : ∀ i, 0 ≤ turn i)
    (hsum : (∑ i, turn i) = 2 * ((n : ℝ) + delta))
    (hdelta : delta < (1 : ℝ) / 2) :
    (∑ i, Nat.floor (turn i)) ≤ 2 * n := by
  apply sum_natFloor_le_of_sum_lt_succ turn (2 * n) hturn0
  rw [hsum]
  push_cast
  linarith

/-- Any obstruction multiplicities bounded pointwise by the floor of the
corresponding normalized hull turn have total count at most 2n. -/
theorem obstruction_count_le_of_turn_slots
    {I : Type*} [Fintype I]
    (turn : I → ℝ) (slots : I → ℕ)
    (n : ℕ) (delta : ℝ)
    (hturn0 : ∀ i, 0 ≤ turn i)
    (hsum : (∑ i, turn i) = 2 * ((n : ℝ) + delta))
    (hdelta : delta < (1 : ℝ) / 2)
    (hslots : ∀ i, slots i ≤ Nat.floor (turn i)) :
    (∑ i, slots i) ≤ 2 * n := by
  have hslotSum :
      (∑ i, slots i) ≤ ∑ i, Nat.floor (turn i) :=
    Finset.sum_le_sum fun i _ => hslots i
  exact hslotSum.trans
    (hull_turn_floor_budget turn n delta hturn0 hsum hdelta)

#print axioms hull_turn_floor_budget
#print axioms obstruction_count_le_of_turn_slots

end JSP000404Research
