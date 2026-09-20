import JSP000404Research.BinaryGainSplit
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Arithmetic hard stop for unconditional balanced binary gain splits

A five-centre exact-normalized geometric realization was found with full
exponents

  [1,0,0,0,0].

For every 2+3 partition, recomputing all survivor exponents at the same fixed
parameter gives at least one survivor with zero gain.  Thus no balanced binary
split satisfies the pointwise +1 hypothesis of BinaryGainSplit.

The geometric realization and angle audit are recorded separately.  This file
formalizes only the exact finite exponent table, so it does not pretend that
floating-point geometry has been kernel-verified.
-/

namespace JSP000404Research

def balancedHardStopOldExp : Fin 5 → ℕ :=
  ![1,0,0,0,0]

/-- The ten two-element sides of the ten unordered 2+3 partitions. -/
def balancedHardStopLeft : Fin 10 → Finset (Fin 5)
  | 0 => {0,1}
  | 1 => {0,2}
  | 2 => {0,3}
  | 3 => {0,4}
  | 4 => {1,2}
  | 5 => {1,3}
  | 6 => {1,4}
  | 7 => {2,3}
  | 8 => {2,4}
  | 9 => {3,4}

/-- Combined child exponent vector for each partition: each coordinate stores
the exponent of that vertex after deleting the opposite child. -/
def balancedHardStopPostExp : Fin 10 → Fin 5 → ℕ
  | 0 => ![2,2,2,1,0]
  | 1 => ![2,2,2,0,0]
  | 2 => ![2,0,0,2,2]
  | 3 => ![2,0,0,2,2]
  | 4 => ![2,2,2,0,0]
  | 5 => ![1,2,1,2,1]
  | 6 => ![1,2,1,1,2]
  | 7 => ![1,1,2,2,1]
  | 8 => ![1,1,2,1,2]
  | 9 => ![2,0,1,2,2]

theorem balancedHardStop_old_weight :
    (∑ v : Fin 5, 2 ^ balancedHardStopOldExp v) = 6 := by
  native_decide

theorem balancedHardStop_left_card
    (r : Fin 10) :
    (balancedHardStopLeft r).card = 2 := by
  fin_cases r <;> native_decide

/-- Every two-element subset of Fin 5 appears exactly once in the table. -/
theorem balancedHardStop_covers_all_two_subsets :
    ∀ A : Finset (Fin 5), A.card = 2 →
      ∃! r : Fin 10, balancedHardStopLeft r = A := by
  native_decide

/-- Every one of the ten balanced partitions has at least one zero-gain
survivor. -/
theorem balancedHardStop_each_split_fails
    (r : Fin 10) :
    ∃ v : Fin 5,
      balancedHardStopPostExp r v <
        balancedHardStopOldExp v + 1 := by
  fin_cases r <;> native_decide

/-- Hence no table entry satisfies the pointwise +1 gain condition. -/
theorem balancedHardStop_no_table_gain_split :
    ¬ ∃ r : Fin 10,
      ∀ v : Fin 5,
        balancedHardStopOldExp v + 1 ≤
          balancedHardStopPostExp r v := by
  rintro ⟨r, hr⟩
  obtain ⟨v, hv⟩ := balancedHardStop_each_split_fails r
  exact (not_lt_of_ge (hr v)) hv

/-- Post-exponent vector on the four-point survivor child after isolating
one singleton leaf.  The isolated coordinate is irrelevant and is filled with
its old exponent. -/
def singletonHardStopPostExp : Fin 5 → Fin 5 → ℕ
  | 0 => ![1,0,0,0,0]
  | 1 => ![1,0,1,0,0]
  | 2 => ![1,1,0,0,0]
  | 3 => ![1,0,0,0,1]
  | 4 => ![1,0,0,1,0]

/-- Every singleton+four split also has a zero-gain survivor in the four-point
child. -/
theorem singletonHardStop_each_split_fails
    (removed : Fin 5) :
    ∃ v : Fin 5,
      v ≠ removed ∧
      singletonHardStopPostExp removed v <
        balancedHardStopOldExp v + 1 := by
  fin_cases removed <;> native_decide

/-- Thus no singleton leaf can be peeled off while making every vertex in the
remaining four-point child gain one exponent unit. -/
theorem singletonHardStop_no_gain_child :
    ¬ ∃ removed : Fin 5,
      ∀ v : Fin 5, v ≠ removed →
        balancedHardStopOldExp v + 1 ≤
          singletonHardStopPostExp removed v := by
  rintro ⟨removed, h⟩
  obtain ⟨v, hne, hv⟩ :=
    singletonHardStop_each_split_fails removed
  exact (not_lt_of_ge (h v hne)) hv

/-- Coverage version: every balanced 2+3 partition is represented by a table
entry, and its realized post-exponent vector violates pointwise +1 gain. -/
theorem balancedHardStop_every_two_three_split_fails :
    ∀ A : Finset (Fin 5), A.card = 2 →
      ∃ r : Fin 10,
        balancedHardStopLeft r = A ∧
        ∃ v : Fin 5,
          balancedHardStopPostExp r v <
            balancedHardStopOldExp v + 1 := by
  intro A hA
  obtain ⟨r, hr, _⟩ :=
    balancedHardStop_covers_all_two_subsets A hA
  exact ⟨r, hr, balancedHardStop_each_split_fails r⟩

#print axioms balancedHardStop_old_weight
#print axioms singletonHardStop_each_split_fails
#print axioms singletonHardStop_no_gain_child
#print axioms balancedHardStop_covers_all_two_subsets
#print axioms balancedHardStop_no_table_gain_split
#print axioms balancedHardStop_every_two_three_split_fails

end JSP000404Research
