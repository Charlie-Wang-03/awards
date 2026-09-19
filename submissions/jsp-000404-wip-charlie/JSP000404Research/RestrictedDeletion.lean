import JSP000404Research.DeletionThreshold
import Mathlib.Tactic

/-!
# Restricted compensated-deletion threshold

For exact-normalized induction one may freeze the at most three top-level
centres containing a triple of points which realizes the global maximum angle.
Deleting any other top-level centre preserves that witness angle, hence the
same angle parameter remains exact.

Accordingly we need a compensated deletion only from a chosen finite candidate
set R.  The sharp pigeonhole threshold localizes perfectly:

if, for every r in R,

  old survivor mass + bonus r <= post r,

then some r in R is compensated as soon as

  sum_{r in R} bonus r >
  sum_{r in R} (weight r - 1).

Equivalently,

  sum_{r in R} weight r <
  card(R) + sum_{r in R} bonus r.

This is strictly weaker than the all-centre threshold when the frozen witness
centres carry substantial weight.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Restricted sharp bonus threshold. -/
theorem exists_compensated_deletion_in_finset
    {V : Type*} [Fintype V]
    (weight post bonus : V → ℕ)
    (R : Finset V)
    (hR : R.Nonempty)
    (hpoint : ∀ r ∈ R,
      (∑ i ∈ Finset.univ.erase r, weight i) + bonus r ≤ post r)
    (hthreshold :
      (∑ r ∈ R, weight r) <
        R.card + ∑ r ∈ R, bonus r) :
    ∃ r ∈ R, (∑ i : V, weight i) ≤ post r := by
  classical
  let W : ℕ := ∑ i : V, weight i
  by_contra hnone
  push_neg at hnone
  have hbonus_point : ∀ r ∈ R, bonus r + 1 ≤ weight r := by
    intro r hr
    have hwr : weight r ≤ W := by
      dsimp [W]
      exact Finset.single_le_sum
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ r)
    have hsplit :
        (∑ i ∈ Finset.univ.erase r, weight i) = W - weight r := by
      dsimp [W]
      rw [Finset.sum_erase (Finset.mem_univ r)]
    have hp := hpoint r hr
    rw [hsplit] at hp
    have hfail : post r < W := by
      dsimp [W]
      exact hnone r hr
    omega
  have hsum :
      ∑ r ∈ R, (bonus r + 1) ≤ ∑ r ∈ R, weight r :=
    Finset.sum_le_sum hbonus_point
  have hleft :
      (∑ r ∈ R, (bonus r + 1)) =
        (∑ r ∈ R, bonus r) + R.card := by
    rw [Finset.sum_add_distrib]
    simp
  rw [hleft] at hsum
  omega

/-- Dyadic specialization. -/
theorem exists_compensated_dyadic_deletion_in_finset
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (post bonus : V → ℕ)
    (R : Finset V)
    (hR : R.Nonempty)
    (hpoint : ∀ r ∈ R,
      (∑ i ∈ Finset.univ.erase r, 2 ^ exponent i) + bonus r ≤ post r)
    (hthreshold :
      (∑ r ∈ R, 2 ^ exponent r) <
        R.card + ∑ r ∈ R, bonus r) :
    ∃ r ∈ R, (∑ i : V, 2 ^ exponent i) ≤ post r :=
  exists_compensated_deletion_in_finset
    (fun i => 2 ^ exponent i) post bonus R hR hpoint hthreshold

#print axioms exists_compensated_deletion_in_finset
#print axioms exists_compensated_dyadic_deletion_in_finset

end JSP000404Research
