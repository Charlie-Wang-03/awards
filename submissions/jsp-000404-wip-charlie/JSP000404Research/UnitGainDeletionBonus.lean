
import JSP000404Research.OverweightStableMax
import JSP000404Research.CompensatedDeletion
import Mathlib.Tactic

/-!
# Canonical dyadic bonus from one-unit deletion gains

For an old exponent profile exponent and a post-deletion exponent table

  after r i,

give survivor i one full old dyadic weight as bonus in deletion column r
exactly when deleting r raises i by at least one exponent unit.

  bonus(i,r) = 2^exponent(i)   if i != r and exponent(i)+1 <= after(r,i),
               0               otherwise.

If survivor exponents never decrease, then pointwise

  old survivor weight + bonus <= post survivor weight.

Therefore every deletion column automatically satisfies the hypothesis used by
OverweightStableMax.

Consequently, if no deletion is compensated, every maximal-exponent centre is
stable in the strongest concrete sense: deleting any other centre cannot raise
its exponent by one full unit.
-/

namespace JSP000404Research

open scoped BigOperators

def unitGainDeletionBonus
    {V : Type*}
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (i r : V) : ℕ :=
  if i ≠ r ∧ exponent i + 1 ≤ after r i then
    2 ^ exponent i
  else
    0

def deletionPostWeight
    {V : Type*} [Fintype V]
    (after : V → V → ℕ)
    (r : V) : ℕ :=
  ∑ i ∈ Finset.univ.erase r, 2 ^ after r i

theorem unitGainDeletionBonus_self_zero
    {V : Type*}
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (r : V) :
    unitGainDeletionBonus exponent after r r = 0 := by
  simp [unitGainDeletionBonus]

theorem unitGainDeletionBonus_eq_weight_of_gain
    {V : Type*}
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    {i r : V}
    (hir : i ≠ r)
    (hgain : exponent i + 1 ≤ after r i) :
    unitGainDeletionBonus exponent after i r =
      2 ^ exponent i := by
  simp [unitGainDeletionBonus, hir, hgain]

theorem unitGainDeletionBonus_eq_zero_of_no_gain
    {V : Type*}
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    {i r : V}
    (hno : ¬ (i ≠ r ∧ exponent i + 1 ≤ after r i)) :
    unitGainDeletionBonus exponent after i r = 0 := by
  simp [unitGainDeletionBonus, hno]

/-- Survivor monotonicity makes the canonical one-unit bonus pointwise valid. -/
theorem old_add_unitGainBonus_le_after_weight
    {V : Type*}
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (hmono :
      ∀ r i, i ≠ r → exponent i ≤ after r i)
    {r i : V}
    (hir : i ≠ r) :
    2 ^ exponent i +
        unitGainDeletionBonus exponent after i r
      ≤
    2 ^ after r i := by
  by_cases hgain : exponent i + 1 ≤ after r i
  · rw [unitGainDeletionBonus_eq_weight_of_gain
      exponent after hir hgain]
    exact two_mul_pow_le_pow_of_succ_le hgain
  · have hbonus :
        unitGainDeletionBonus exponent after i r = 0 := by
      apply unitGainDeletionBonus_eq_zero_of_no_gain
      push_neg
      intro _
      exact hgain
    rw [hbonus, add_zero]
    exact Nat.pow_le_pow_right
      (by norm_num : 0 < 2)
      (hmono r i hir)

/-- Column form: old survivor mass plus all canonical gain bonuses is bounded
by the actual post-deletion survivor mass. -/
theorem unitGainDeletionBonus_column_bound
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (hmono :
      ∀ r i, i ≠ r → exponent i ≤ after r i)
    (r : V) :
    (∑ i ∈ Finset.univ.erase r, 2 ^ exponent i) +
        (∑ i : V,
          unitGainDeletionBonus exponent after i r)
      ≤
    deletionPostWeight after r := by
  classical
  have hbonusErase :
      (∑ i : V,
        unitGainDeletionBonus exponent after i r)
      =
      ∑ i ∈ Finset.univ.erase r,
        unitGainDeletionBonus exponent after i r := by
    have h :=
      Finset.sum_erase_add
        (Finset.univ : Finset V)
        (fun i =>
          unitGainDeletionBonus exponent after i r)
        (Finset.mem_univ r)
    rw [unitGainDeletionBonus_self_zero] at h
    simpa [add_zero] using h.symm
  rw [hbonusErase, ← Finset.sum_add_distrib]
  unfold deletionPostWeight
  apply Finset.sum_le_sum
  intro i hi
  have hir : i ≠ r := by
    simpa using (Finset.mem_erase.mp hi).1
  exact old_add_unitGainBonus_le_after_weight
    exponent after hmono hir

/-- BonusStable for the canonical matrix is exactly enough to forbid any
one-unit gain under deleting another centre. -/
theorem no_unit_gain_of_unitGainBonusStable
    {V : Type*}
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    {i : V}
    (hstable :
      BonusStable exponent
        (unitGainDeletionBonus exponent after) i) :
    ∀ r, i ≠ r →
      ¬ exponent i + 1 ≤ after r i := by
  intro r hir hgain
  have hbonus :=
    unitGainDeletionBonus_eq_weight_of_gain
      exponent after hir hgain
  have hlt := hstable r
  rw [hbonus] at hlt
  exact (lt_irrefl _ hlt)

/-- Main maximal-centre consequence.

If every survivor exponent is monotone and no deletion preserves the full old
mass, then any maximal-exponent centre has zero full-unit gain under deletion
of every other centre.
-/
theorem maximal_exponent_no_unit_gain_of_no_compensated
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (hmono :
      ∀ r i, i ≠ r → exponent i ≤ after r i)
    (hnocomp :
      ∀ r,
        deletionPostWeight after r <
          ∑ i : V, 2 ^ exponent i)
    (i : V)
    (hmax : ∀ j, exponent j ≤ exponent i) :
    ∀ r, i ≠ r →
      ¬ exponent i + 1 ≤ after r i := by
  have hstable :
      BonusStable exponent
        (unitGainDeletionBonus exponent after) i := by
    apply bonusStable_of_max_exponent_of_no_compensated
      exponent (deletionPostWeight after)
      (unitGainDeletionBonus exponent after)
  · intro r
    exact unitGainDeletionBonus_column_bound
      exponent after hmono r
  · exact hnocomp
  · exact hmax
  exact no_unit_gain_of_unitGainBonusStable
    exponent after hstable

/-- Contrapositive: one full gain at a maximal centre forces some compensated
deletion. -/
theorem exists_compensated_deletion_of_maximal_unit_gain
    {V : Type*} [Fintype V] [Nonempty V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (hmono :
      ∀ r i, i ≠ r → exponent i ≤ after r i)
    (i : V)
    (hmax : ∀ j, exponent j ≤ exponent i)
    (hgain :
      ∃ r, i ≠ r ∧ exponent i + 1 ≤ after r i) :
    ∃ r,
      (∑ j : V, 2 ^ exponent j) ≤
        deletionPostWeight after r := by
  obtain ⟨r, hir, hgainIR⟩ := hgain
  apply exists_compensated_deletion_of_max_exponent_self_bonus
    exponent
    (deletionPostWeight after)
    (unitGainDeletionBonus exponent after)
    (unitGainDeletionBonus_column_bound
      exponent after hmono)
    i hmax
  exact ⟨r, by
    rw [unitGainDeletionBonus_eq_weight_of_gain
      exponent after hir hgainIR]⟩

#print axioms unitGainDeletionBonus_column_bound
#print axioms no_unit_gain_of_unitGainBonusStable
#print axioms maximal_exponent_no_unit_gain_of_no_compensated
#print axioms exists_compensated_deletion_of_maximal_unit_gain

end JSP000404Research
