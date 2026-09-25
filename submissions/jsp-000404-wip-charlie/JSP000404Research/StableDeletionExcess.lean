
import JSP000404Research.DeletionThreshold
import Mathlib.Tactic

/-!
# Stable weight can be paid by excess deletion bonus

StableDeletionReduction discards every amount of row bonus beyond the first
copy of a nonstable centre's old weight.  This is sometimes too coarse: a
gain-two merge produces three old-weight copies of bonus, and the extra copies
can pay genuinely stable high-weight centres such as a sharp top centre.

For each centre i let

  rowBonus(i) = sum_r bonus(i,r).

Choose a set U of nonstable centres for which weight(i) <= rowBonus(i).
Define the row excess

  excess(i) = rowBonus(i) - weight(i),  i in U.

Then

  totalBonus
    >= sum_{i in U} weight(i) + sum_{i in U} excess(i).

After splitting the original weight into U and its stable complement, the
sharp deletion threshold reduces to

  stableWeight
    < card(V) + totalExcess.

This strictly strengthens the earlier criterion stableWeight < card(V).
-/

namespace JSP000404Research

open scoped BigOperators

def rowDeletionBonus
    {V R : Type*} [Fintype R]
    (bonus : V → R → ℕ)
    (i : V) : ℕ :=
  ∑ r : R, bonus i r

def rowExcess
    {V R : Type*} [Fintype R]
    (weight : V → ℕ)
    (bonus : V → R → ℕ)
    (i : V) : ℕ :=
  rowDeletionBonus bonus i - weight i

theorem weight_add_rowExcess_eq_rowBonus_of_le
    {V R : Type*} [Fintype R]
    (weight : V → ℕ)
    (bonus : V → R → ℕ)
    (i : V)
    (hpay : weight i ≤ rowDeletionBonus bonus i) :
    weight i + rowExcess weight bonus i =
      rowDeletionBonus bonus i := by
  unfold rowExcess
  omega

theorem selected_weight_add_excess_le_total_matrix_bonus
    {I R : Type*} [Fintype I] [Fintype R]
    (weight : I → ℕ)
    (bonus : I → R → ℕ)
    (U : Finset I)
    (hpay :
      ∀ i ∈ U, weight i ≤ rowDeletionBonus bonus i) :
    (∑ i ∈ U, weight i) +
        (∑ i ∈ U, rowExcess weight bonus i)
      ≤
    ∑ r : R, ∑ i : I, bonus i r := by
  classical
  have hEq :
      (∑ i ∈ U, weight i) +
          (∑ i ∈ U, rowExcess weight bonus i)
        =
      ∑ i ∈ U, rowDeletionBonus bonus i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact weight_add_rowExcess_eq_rowBonus_of_le
      weight bonus i (hpay i hi)
  rw [hEq]
  calc
    (∑ i ∈ U, rowDeletionBonus bonus i)
        ≤ ∑ i : I, rowDeletionBonus bonus i := by
          exact Finset.sum_le_sum_of_subset
            (Finset.subset_univ U)
    _ = ∑ r : R, ∑ i : I, bonus i r := by
          unfold rowDeletionBonus
          exact Finset.sum_comm

/-- Sharp compensated-deletion criterion retaining all excess row bonus. -/
theorem exists_compensated_deletion_of_stable_weight_lt_card_add_excess
    {V : Type*} [Fintype V] [Nonempty V]
    (weight post : V → ℕ)
    (bonus : V → V → ℕ)
    (unstable : Finset V)
    (hpoint : ∀ r,
      (∑ i ∈ Finset.univ.erase r, weight i) +
          (∑ i : V, bonus i r) ≤ post r)
    (hpay :
      ∀ i ∈ unstable,
        weight i ≤ rowDeletionBonus bonus i)
    (hstable :
      (∑ i ∈ (Finset.univ : Finset V) \ unstable, weight i)
        <
      Fintype.card V +
        ∑ i ∈ unstable, rowExcess weight bonus i) :
    ∃ r : V, (∑ i : V, weight i) ≤ post r := by
  classical
  have hbonus :
      (∑ i ∈ unstable, weight i) +
          (∑ i ∈ unstable, rowExcess weight bonus i)
        ≤
      ∑ r : V, ∑ i : V, bonus i r :=
    selected_weight_add_excess_le_total_matrix_bonus
      weight bonus unstable hpay
  have hsplit :
      (∑ i : V, weight i) =
        (∑ i ∈ unstable, weight i) +
          (∑ i ∈ (Finset.univ : Finset V) \ unstable, weight i) := by
    rw [← Finset.sum_union]
    · apply Finset.sum_congr
      · ext i
        simp
      · intro i hi
        rfl
    · exact Finset.disjoint_sdiff_right
  apply exists_compensated_deletion_of_bonus_threshold
    weight post (fun r => ∑ i : V, bonus i r) hpoint
  rw [hsplit]
  omega

/-- Dyadic specialization. -/
theorem exists_compensated_deletion_of_dyadic_stable_weight_lt_card_add_excess
    {V : Type*} [Fintype V] [Nonempty V]
    (exponent : V → ℕ)
    (post : V → ℕ)
    (bonus : V → V → ℕ)
    (unstable : Finset V)
    (hpoint : ∀ r,
      (∑ i ∈ Finset.univ.erase r, 2 ^ exponent i) +
          (∑ i : V, bonus i r) ≤ post r)
    (hpay :
      ∀ i ∈ unstable,
        2 ^ exponent i ≤ rowDeletionBonus bonus i)
    (hstable :
      (∑ i ∈ (Finset.univ : Finset V) \ unstable,
          2 ^ exponent i)
        <
      Fintype.card V +
        ∑ i ∈ unstable,
          rowExcess (fun j => 2 ^ exponent j) bonus i) :
    ∃ r : V, (∑ i : V, 2 ^ exponent i) ≤ post r :=
  exists_compensated_deletion_of_stable_weight_lt_card_add_excess
    (fun i => 2 ^ exponent i) post bonus unstable
    hpoint hpay hstable

#print axioms selected_weight_add_excess_le_total_matrix_bonus
#print axioms exists_compensated_deletion_of_stable_weight_lt_card_add_excess
#print axioms exists_compensated_deletion_of_dyadic_stable_weight_lt_card_add_excess

end JSP000404Research
