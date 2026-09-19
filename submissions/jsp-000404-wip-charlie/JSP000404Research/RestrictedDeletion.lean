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
  have hfail : ∀ r ∈ R, post r + 1 ≤ W := by
    intro r hr
    dsimp [W]
    omega
  have hpoint' : ∀ r ∈ R,
      W - weight r + bonus r ≤ post r := by
    intro r hr
    have hsplit :
        (∑ i ∈ Finset.univ.erase r, weight i) = W - weight r := by
      dsimp [W]
      rw [Finset.sum_erase (Finset.mem_univ r)]
    simpa [hsplit] using hpoint r hr
  have hsum :
      ∑ r ∈ R, (W - weight r + bonus r + 1) ≤
        ∑ r ∈ R, W := by
    apply Finset.sum_le_sum
    intro r hr
    exact (Nat.add_le_add_right (hpoint' r hr) 1).trans (hfail r hr)
  have hweight_le : ∀ r ∈ R, weight r ≤ W := by
    intro r hr
    dsimp [W]
    exact Finset.single_le_sum
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ r)
  have hrewrite :
      (∑ r ∈ R, (W - weight r + bonus r + 1)) =
        R.card * W - (∑ r ∈ R, weight r) +
          (∑ r ∈ R, bonus r) + R.card := by
    -- Pure natural-number bookkeeping; all deleted weights are bounded by W.
    omega
  rw [hrewrite] at hsum
  have hconst : (∑ _r ∈ R, W) = R.card * W := by
    simp [Nat.mul_comm]
  rw [hconst] at hsum
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
