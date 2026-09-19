import JSP000404Research.CompensatedDeletion
import Mathlib.Tactic

/-!
# Averaging criterion for compensated deletion

For a finite nonempty set of top-level centres, let

  W = sum_i weight i

be the original total weight, and let `post r` be the total surviving weight
after deleting centre `r`.

Instead of guessing a deletable centre, it is enough to prove the average bound

  card(V) * W <= sum_r post r.

Then some deletion satisfies `W <= post r`.

A useful double-counting form introduces a nonnegative deletion bonus
`bonus r`.  The old survivor sums, averaged over all deletions, account for
exactly `card(V)-1` copies of every original weight.  Therefore if the total
bonus over all deletions pays one further copy of `W`, some deletion is
compensated.

This is the abstract form of the local-merge-bonus strategy for JSP-000404.
-/

namespace JSP000404Research

open scoped BigOperators

/-- If the average post-deletion mass is at least the original target, one
individual deletion attains the target. -/
theorem exists_post_ge_of_average
    {V : Type*} [Fintype V] [Nonempty V]
    (post : V → ℕ) (target : ℕ)
    (havg : Fintype.card V * target ≤ ∑ r : V, post r) :
    ∃ r : V, target ≤ post r := by
  classical
  by_contra hnone
  push_neg at hnone
  have hlt :
      (∑ r : V, post r) < ∑ _r : V, target := by
    exact Finset.sum_lt_sum_of_nonempty
      Finset.univ_nonempty (fun r _ => hnone r)
  have hconst :
      (∑ _r : V, target) = Fintype.card V * target := by
    simp
  rw [hconst] at hlt
  omega

/-- Double-counting identity: for each deletion, sum the old weights of all
survivors.  Adding one copy of the full old total gives exactly
`card(V)` copies of that total. -/
theorem survivor_double_count
    {V : Type*} [Fintype V]
    (weight : V → ℕ) :
    (∑ r : V, ∑ i ∈ Finset.univ.erase r, weight i) +
        (∑ i : V, weight i)
      =
    Fintype.card V * (∑ i : V, weight i) := by
  classical
  rw [← Finset.sum_add_distrib]
  calc
    (∑ r : V,
        (∑ i ∈ Finset.univ.erase r, weight i) + weight r)
        =
        ∑ _r : V, (∑ i : V, weight i) := by
          apply Finset.sum_congr rfl
          intro r _
          exact Finset.sum_erase_add _ _ (Finset.mem_univ r)
    _ = Fintype.card V * (∑ i : V, weight i) := by
      simp

/-- If each post-deletion total absorbs its old survivor total plus a chosen
bonus, and the bonuses collectively pay one full copy of the original total,
then the average post-deletion total is at least the original total. -/
theorem average_post_ge_of_bonus
    {V : Type*} [Fintype V]
    (weight post bonus : V → ℕ)
    (hpoint : ∀ r,
      (∑ i ∈ Finset.univ.erase r, weight i) + bonus r ≤ post r)
    (hbonus :
      (∑ i : V, weight i) ≤ ∑ r : V, bonus r) :
    Fintype.card V * (∑ i : V, weight i) ≤
      ∑ r : V, post r := by
  classical
  have hsum :
      ∑ r : V,
          ((∑ i ∈ Finset.univ.erase r, weight i) + bonus r)
        ≤ ∑ r : V, post r :=
    Finset.sum_le_sum (fun r _ => hpoint r)
  rw [Finset.sum_add_distrib] at hsum
  have hdc := survivor_double_count weight
  omega

/-- Consequently, a collective bonus of one full original weight guarantees
the existence of an individually compensated deletion. -/
theorem exists_compensated_deletion_of_bonus_average
    {V : Type*} [Fintype V] [Nonempty V]
    (weight post bonus : V → ℕ)
    (hpoint : ∀ r,
      (∑ i ∈ Finset.univ.erase r, weight i) + bonus r ≤ post r)
    (hbonus :
      (∑ i : V, weight i) ≤ ∑ r : V, bonus r) :
    ∃ r : V, (∑ i : V, weight i) ≤ post r := by
  apply exists_post_ge_of_average post (∑ i : V, weight i)
  exact average_post_ge_of_bonus weight post bonus hpoint hbonus

/-- Dyadic exponent specialization. -/
theorem exists_compensated_deletion_of_dyadic_bonus
    {V : Type*} [Fintype V] [Nonempty V]
    (exponent : V → ℕ)
    (post bonus : V → ℕ)
    (hpoint : ∀ r,
      (∑ i ∈ Finset.univ.erase r, 2 ^ exponent i) + bonus r ≤ post r)
    (hbonus :
      (∑ i : V, 2 ^ exponent i) ≤ ∑ r : V, bonus r) :
    ∃ r : V, (∑ i : V, 2 ^ exponent i) ≤ post r :=
  exists_compensated_deletion_of_bonus_average
    (fun i => 2 ^ exponent i) post bonus hpoint hbonus

#print axioms exists_post_ge_of_average
#print axioms survivor_double_count
#print axioms average_post_ge_of_bonus
#print axioms exists_compensated_deletion_of_bonus_average
#print axioms exists_compensated_deletion_of_dyadic_bonus

end JSP000404Research
