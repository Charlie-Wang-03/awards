import JSP000404Research.DeletionThreshold
import Mathlib.Tactic

/-!
# Reducing compensated deletion to stable centres

For a survivor i, call it nonstable if at least one deletion creates enough
merge bonus to pay one full copy of its old weight.  Summing over all
deletions, every nonstable centre therefore pays for itself at least once.

The sharp deletion threshold from DeletionThreshold only asks

  W < card(V) + totalBonus.

Hence all nonstable weight cancels automatically.  It is enough that the
total old weight of the remaining stable centres be strictly below card(V).

For dyadic Sendov weights, a single exponent gain already supplies one full old
weight, so this is exactly the reduction needed after the local merge-gain
classification.
-/

namespace JSP000404Research

open scoped BigOperators

/-- A selected family of rows, each of which has one column paying its full
row weight, is collectively paid by the whole bonus matrix. -/
theorem selected_weight_le_total_matrix_bonus
    {I R : Type*} [Fintype I] [Fintype R]
    (weight : I → ℕ)
    (bonus : I → R → ℕ)
    (U : Finset I)
    (hpayer : ∀ i ∈ U, ∃ r : R, weight i ≤ bonus i r) :
    (∑ i ∈ U, weight i) ≤
      ∑ r : R, ∑ i : I, bonus i r := by
  classical
  have hrow :
      ∀ i ∈ U, weight i ≤ ∑ r : R, bonus i r := by
    intro i hi
    obtain ⟨r, hir⟩ := hpayer i hi
    exact hir.trans
      (Finset.single_le_sum
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ r))
  have hsum :
      (∑ i ∈ U, weight i) ≤
        ∑ i ∈ U, ∑ r : R, bonus i r :=
    Finset.sum_le_sum fun i hi => hrow i hi
  have hsub :
      (∑ i ∈ U, ∑ r : R, bonus i r) ≤
        ∑ i : I, ∑ r : R, bonus i r := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ U)
      (fun _ _ _ => Nat.zero_le _)
  calc
    (∑ i ∈ U, weight i)
        ≤ ∑ i : I, ∑ r : R, bonus i r := hsum.trans hsub
    _ = ∑ r : R, ∑ i : I, bonus i r := by
      exact Finset.sum_comm

/-- If every nonstable row pays for itself and the complementary stable weight
is below the number of deletion choices, the sharp average threshold is met. -/
theorem exists_compensated_deletion_of_stable_weight_lt_card
    {V : Type*} [Fintype V] [Nonempty V]
    (weight post : V → ℕ)
    (bonus : V → V → ℕ)
    (unstable : Finset V)
    (hpoint : ∀ r,
      (∑ i ∈ Finset.univ.erase r, weight i) +
          (∑ i : V, bonus i r) ≤ post r)
    (hpayer : ∀ i ∈ unstable,
      ∃ r : V, weight i ≤ bonus i r)
    (hstable :
      (∑ i ∈ (Finset.univ : Finset V) \ unstable, weight i) <
        Fintype.card V) :
    ∃ r : V, (∑ i : V, weight i) ≤ post r := by
  classical
  have hpaid :
      (∑ i ∈ unstable, weight i) ≤
        ∑ r : V, ∑ i : V, bonus i r :=
    selected_weight_le_total_matrix_bonus
      weight bonus unstable hpayer
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

/-- Dyadic specialization: stable centres are precisely the rows for which no
incident deletion provides a one-old-weight bonus. -/
theorem exists_compensated_deletion_of_dyadic_stable_weight_lt_card
    {V : Type*} [Fintype V] [Nonempty V]
    (exponent : V → ℕ)
    (post : V → ℕ)
    (bonus : V → V → ℕ)
    (unstable : Finset V)
    (hpoint : ∀ r,
      (∑ i ∈ Finset.univ.erase r, 2 ^ exponent i) +
          (∑ i : V, bonus i r) ≤ post r)
    (hpayer : ∀ i ∈ unstable,
      ∃ r : V, 2 ^ exponent i ≤ bonus i r)
    (hstable :
      (∑ i ∈ (Finset.univ : Finset V) \ unstable,
          2 ^ exponent i) < Fintype.card V) :
    ∃ r : V, (∑ i : V, 2 ^ exponent i) ≤ post r :=
  exists_compensated_deletion_of_stable_weight_lt_card
    (fun i => 2 ^ exponent i) post bonus unstable
    hpoint hpayer hstable

#print axioms selected_weight_le_total_matrix_bonus
#print axioms exists_compensated_deletion_of_stable_weight_lt_card
#print axioms exists_compensated_deletion_of_dyadic_stable_weight_lt_card

end JSP000404Research
