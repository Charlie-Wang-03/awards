import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Exact aggregate-split hard stop table

A simple five-point integer planar realization (documented separately) has
fixed-t root exponent vector

  [4,1,1,1,1]

at n=5, hence root dyadic mass 24.

For its ten nontrivial 2+3 partitions, the exact old/post child mass table is
recorded below.  Every row fails the aggregate doubling condition on at least
one side.

This file formalizes only the finite arithmetic table.  The Euclidean
realization and floor-margin audit live in the companion Markdown note.
-/

namespace JSP000404Research

open scoped BigOperators

structure AggregateSplitMassRow where
  oldA : ℕ
  postA : ℕ
  oldB : ℕ
  postB : ℕ
deriving DecidableEq, Repr

def aggregateExistenceHardStopOldExp : Fin 5 → ℕ :=
  ![4,1,1,1,1]

def aggregateExistenceHardStopRows : Fin 10 → AggregateSplitMassRow :=
  ![
    ⟨18,32,6,32⟩,
    ⟨18,32,6,28⟩,
    ⟨18,32,6,32⟩,
    ⟨18,32,6,28⟩,
    ⟨20,28,4,32⟩,
    ⟨20,32,4,32⟩,
    ⟨20,24,4,32⟩,
    ⟨20,24,4,32⟩,
    ⟨20,24,4,32⟩,
    ⟨20,32,4,32⟩
  ]

theorem aggregateExistenceHardStop_root_weight :
    (∑ v : Fin 5, 2 ^ aggregateExistenceHardStopOldExp v) = 24 := by
  native_decide

theorem aggregateExistenceHardStop_root_capacity :
    (∑ v : Fin 5, 2 ^ aggregateExistenceHardStopOldExp v) ≤ 2 ^ 5 := by
  native_decide

/-- No listed 2+3 partition doubles the old dyadic mass on both children. -/
theorem aggregateExistenceHardStop_every_row_fails
    (r : Fin 10) :
    ¬ (
      2 * (aggregateExistenceHardStopRows r).oldA
        ≤ (aggregateExistenceHardStopRows r).postA ∧
      2 * (aggregateExistenceHardStopRows r).oldB
        ≤ (aggregateExistenceHardStopRows r).postB
    ) := by
  fin_cases r <;> native_decide

/-- Therefore the finite table contains no aggregate-doubling first split. -/
theorem aggregateExistenceHardStop_no_row :
    ¬ ∃ r : Fin 10,
      2 * (aggregateExistenceHardStopRows r).oldA
          ≤ (aggregateExistenceHardStopRows r).postA ∧
      2 * (aggregateExistenceHardStopRows r).oldB
          ≤ (aggregateExistenceHardStopRows r).postB := by
  intro h
  obtain ⟨r, hr⟩ := h
  exact aggregateExistenceHardStop_every_row_fails r hr

/-- The best possible side ratio in the table is already bounded away from
one: the first four rows fail with 32 < 2*18. -/
theorem aggregateExistenceHardStop_pair_side_gap :
    ∀ r : Fin 4,
      (aggregateExistenceHardStopRows
        ⟨r.val, by omega⟩).postA <
      2 * (aggregateExistenceHardStopRows
        ⟨r.val, by omega⟩).oldA := by
  intro r
  fin_cases r <;> native_decide

#print axioms aggregateExistenceHardStop_root_weight
#print axioms aggregateExistenceHardStop_every_row_fails
#print axioms aggregateExistenceHardStop_no_row

end JSP000404Research
