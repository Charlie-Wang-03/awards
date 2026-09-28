import JSP000404Research.SharpSupportThreeDeletionGain
import JSP000404Research.ConcreteCentreDeletionMonotone
import Mathlib.Tactic

/-!
# Four support-three gains compensate deletion of the six-point sharp top

The six-point terminal profile has dyadic mass

  2^(n-1) + 5 * 2^(n-3) = 9 * 2^(n-3).

After deleting the sharp top, every surviving minimum is exponent-monotone.
Every support-three minimum gains at least one exponent unit.

Hence, if four of the five minima are support-three, the child mass is at
least

  4 * 2^(n-2) + 1 * 2^(n-3)
    = 9 * 2^(n-3),

exactly enough to compensate removal of the top centre.

This file first isolates the finite arithmetic statement.  It is the weight
ledger needed to feed SharpSupportThreeDeletionGain into the overweight-only
minimal-counterexample induction.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Pure five-survivor weight ledger. -/
theorem five_survivor_weight_ge_six_point_profile_of_four_gains
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ}
    (hn : 3 ≤ n)
    (top : V)
    (hcard : Fintype.card V = 6)
    (childExponent : V → ℕ)
    (good : Finset V)
    (hgoodSub :
      good ⊆ (Finset.univ.erase top : Finset V))
    (hgoodCard : good.card = 4)
    (hbase :
      ∀ v : V, v ≠ top →
        n - 3 ≤ childExponent v)
    (hgain :
      ∀ v ∈ good,
        n - 2 ≤ childExponent v) :
    2 ^ (n - 1) + 5 * 2 ^ (n - 3)
      ≤
    ∑ v ∈ (Finset.univ.erase top : Finset V),
      2 ^ childExponent v := by
  let S : Finset V := Finset.univ.erase top
  let R : Finset V := S \ good
  have hScard : S.card = 5 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ top),
        Finset.card_univ, hcard]
  have hRcard : R.card = 1 := by
    dsimp [R]
    rw [Finset.card_sdiff hgoodSub, hScard, hgoodCard]
  have hgoodLower :
      4 * 2 ^ (n - 2)
        ≤
      ∑ v ∈ good, 2 ^ childExponent v := by
    calc
      4 * 2 ^ (n - 2)
          = ∑ _v ∈ good, 2 ^ (n - 2) := by
              simp [hgoodCard, Nat.mul_comm]
      _ ≤ ∑ v ∈ good, 2 ^ childExponent v := by
            exact Finset.sum_le_sum
              (fun v hv =>
                Nat.pow_le_pow_right
                  (by norm_num : 0 < 2)
                  (hgain v hv))
  have hrestLower :
      2 ^ (n - 3)
        ≤
      ∑ v ∈ R, 2 ^ childExponent v := by
    calc
      2 ^ (n - 3)
          = ∑ _v ∈ R, 2 ^ (n - 3) := by
              simp [hRcard]
      _ ≤ ∑ v ∈ R, 2 ^ childExponent v := by
            exact Finset.sum_le_sum
              (fun v hv => by
                apply Nat.pow_le_pow_right
                  (by norm_num : 0 < 2)
                apply hbase v
                have hvS : v ∈ S := by
                  exact (Finset.mem_sdiff.mp hv).1
                simpa [S] using hvS)
  have hsplit :
      (∑ v ∈ S, 2 ^ childExponent v)
        =
      (∑ v ∈ good, 2 ^ childExponent v) +
      (∑ v ∈ R, 2 ^ childExponent v) := by
    have hsd :=
      Finset.sum_sdiff hgoodSub
        (fun v => 2 ^ childExponent v)
    dsimp [R]
    omega
  have hchild :
      4 * 2 ^ (n - 2) + 2 ^ (n - 3)
        ≤
      ∑ v ∈ S, 2 ^ childExponent v := by
    rw [hsplit]
    omega
  have hn2 : n - 2 = (n - 3) + 1 := by omega
  have hn1 : n - 1 = (n - 3) + 2 := by omega
  rw [hn2, hn1, pow_add, pow_add] at hchild ⊢
  norm_num at hchild ⊢
  simpa [S, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using hchild

#print axioms five_survivor_weight_ge_six_point_profile_of_four_gains

end JSP000404Research
