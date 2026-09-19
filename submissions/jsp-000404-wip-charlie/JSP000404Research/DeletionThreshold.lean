import JSP000404Research.DeletionAveraging
import Mathlib.Tactic

/-!
# Sharp total-bonus threshold for compensated deletion

The averaging criterion in DeletionAveraging asks for total deletion bonus at
least one full copy of the original weight W.  That is sufficient but stronger
than necessary.

Assume every post-deletion total dominates

  old survivor mass + bonus r.

If no deletion is compensated, then post r < W for every r.  Since all
quantities are natural numbers this gives post r + 1 <= W.  Summing over all
r and using the survivor double-count identity shows

  sum_r bonus r <= W - |V|.

Hence the sharp pigeonhole threshold is

  W < |V| + sum_r bonus r.

Above this threshold some deletion must satisfy W <= post r.
-/

namespace JSP000404Research

open scoped BigOperators

/-- A total bonus exceeding W-|V| forces an individually compensated
deletion.  The hypothesis is written without natural subtraction. -/
theorem exists_compensated_deletion_of_bonus_threshold
    {V : Type*} [Fintype V] [Nonempty V]
    (weight post bonus : V → ℕ)
    (hpoint : ∀ r,
      (∑ i ∈ Finset.univ.erase r, weight i) + bonus r ≤ post r)
    (hthreshold :
      (∑ i : V, weight i) <
        Fintype.card V + ∑ r : V, bonus r) :
    ∃ r : V, (∑ i : V, weight i) ≤ post r := by
  classical
  let W : ℕ := ∑ i : V, weight i
  by_contra hnone
  push_neg at hnone
  have hsumLower :
      (∑ r : V, ∑ i ∈ Finset.univ.erase r, weight i) +
          (∑ r : V, bonus r)
        ≤ ∑ r : V, post r := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun r _ => hpoint r
  have hsumUpper :
      (∑ r : V, post r) + Fintype.card V ≤
        Fintype.card V * W := by
    have hp : ∀ r : V, post r + 1 ≤ W := by
      intro r
      dsimp [W]
      omega
    have hs :
        ∑ r : V, (post r + 1) ≤ ∑ _r : V, W :=
      Finset.sum_le_sum fun r _ => hp r
    simpa [Finset.sum_add_distrib, W] using hs
  have hdc := survivor_double_count weight
  dsimp [W] at hsumUpper
  omega

/-- Dyadic specialization for Sendov cluster exponents. -/
theorem exists_compensated_deletion_of_dyadic_bonus_threshold
    {V : Type*} [Fintype V] [Nonempty V]
    (exponent : V → ℕ)
    (post bonus : V → ℕ)
    (hpoint : ∀ r,
      (∑ i ∈ Finset.univ.erase r, 2 ^ exponent i) + bonus r ≤ post r)
    (hthreshold :
      (∑ i : V, 2 ^ exponent i) <
        Fintype.card V + ∑ r : V, bonus r) :
    ∃ r : V, (∑ i : V, 2 ^ exponent i) ≤ post r :=
  exists_compensated_deletion_of_bonus_threshold
    (fun i => 2 ^ exponent i) post bonus hpoint hthreshold

#print axioms exists_compensated_deletion_of_bonus_threshold
#print axioms exists_compensated_deletion_of_dyadic_bonus_threshold

end JSP000404Research
