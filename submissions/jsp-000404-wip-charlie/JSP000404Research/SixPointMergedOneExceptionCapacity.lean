import JSP000404Research.BinaryEdgePartition
import Mathlib.Tactic

/-!
# Six-point weighted terminal with one minimum allowed one extra colour

For the six-point terminal profile

  top exponent    = n-1,
  five minima     = n-3,

an n-colour binary edge partition does not need every minimum to meet its
exact local active-colour budget.

Suppose

* the top uses at most one active colour;
* one distinguished non-top minimum may use at most four active colours;
* every other minimum uses at most three.

Weighted Hansel then receives at least

  2^(n-1) + 2^(n-4) + 4 * 2^(n-3)
    = 17 * 2^(n-4)

from the six vertices, while the n-cube has only

  2^n = 16 * 2^(n-4).

Thus such a partition is impossible for n>=4.

This is the correct relaxed capacity outlet for the final phase search:
boundary-colour properness is still global, but saturation failure may survive
at one minimum centre.
-/

namespace JSP000404Research

open scoped BigOperators

theorem six_point_weight_lower_of_one_min_exception
    {V : Type*} [Fintype V]
    (n : ℕ)
    (hn : 4 ≤ n)
    (top bad : V)
    (htb : top ≠ bad)
    (active : V → ℕ)
    (hcard : Fintype.card V = 6)
    (hTop : active top ≤ 1)
    (hBad : active bad ≤ 4)
    (hOther :
      ∀ v : V, v ≠ top → v ≠ bad → active v ≤ 3) :
    17 * 2 ^ (n - 4) ≤
      ∑ v : V, 2 ^ (n - active v) := by
  classical
  let S : Finset V := (Finset.univ.erase top).erase bad
  have hbadMemErase :
      bad ∈ (Finset.univ.erase top : Finset V) := by
    simp [htb]
  have hScard : S.card = 4 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem hbadMemErase,
        Finset.card_erase_of_mem (Finset.mem_univ top)]
    simp [hcard]
  have htopPow :
      2 ^ (n - 1) ≤ 2 ^ (n - active top) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  have hbadPow :
      2 ^ (n - 4) ≤ 2 ^ (n - active bad) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  have hotherPow :
      ∀ v ∈ S,
        2 ^ (n - 3) ≤ 2 ^ (n - active v) := by
    intro v hv
    have hvt : v ≠ top := by
      dsimp [S] at hv
      exact (Finset.mem_erase.mp
        (Finset.mem_of_mem_erase hv)).1
    have hvb : v ≠ bad := by
      dsimp [S] at hv
      exact (Finset.mem_erase.mp hv).1
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    have ha := hOther v hvt hvb
    omega
  have hsumS :
      S.card * 2 ^ (n - 3) ≤
        ∑ v ∈ S, 2 ^ (n - active v) := by
    calc
      S.card * 2 ^ (n - 3)
          = ∑ _v ∈ S, 2 ^ (n - 3) := by
              simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ S, 2 ^ (n - active v) := by
            exact Finset.sum_le_sum
              (fun v hv => hotherPow v hv)
  have hdecomp :
      (∑ v : V, 2 ^ (n - active v)) =
        2 ^ (n - active top) +
          2 ^ (n - active bad) +
          ∑ v ∈ S, 2 ^ (n - active v) := by
    rw [← Finset.sum_erase_add
      (fun v => 2 ^ (n - active v))
      (Finset.mem_univ top)]
    have hbadIn :
        bad ∈ (Finset.univ.erase top : Finset V) := hbadMemErase
    rw [← Finset.sum_erase_add
      (fun v => 2 ^ (n - active v)) hbadIn]
    dsimp [S]
    omega
  have hlower :
      2 ^ (n - 1) + 2 ^ (n - 4) +
          4 * 2 ^ (n - 3)
        ≤
      ∑ v : V, 2 ^ (n - active v) := by
    rw [hdecomp]
    rw [← hScard] at hsumS
    omega
  have hn1 : n - 1 = (n - 4) + 3 := by omega
  have hn3 : n - 3 = (n - 4) + 1 := by omega
  rw [hn1, hn3, pow_add, pow_add] at hlower
  norm_num at hlower
  simpa [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlower

/-- No n-colour binary edge partition can realize the relaxed six-point
one-exception palette profile. -/
theorem no_six_point_partition_with_one_min_exception
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (hn : 4 ≤ n)
    (P : BinaryEdgePartition V n)
    (top bad : V)
    (htb : top ≠ bad)
    (hcard : Fintype.card V = 6)
    (hTop :
      (BinaryEdgePartition.active P top).card ≤ 1)
    (hBad :
      (BinaryEdgePartition.active P bad).card ≤ 4)
    (hOther :
      ∀ v : V, v ≠ top → v ≠ bad →
        (BinaryEdgePartition.active P v).card ≤ 3) :
    False := by
  have hlower :=
    six_point_weight_lower_of_one_min_exception
      n hn top bad htb
      (fun v => (BinaryEdgePartition.active P v).card)
      hcard hTop hBad hOther
  have hupper := BinaryEdgePartition.weighted_capacity P
  have hpow :
      2 ^ n = 16 * 2 ^ (n - 4) := by
    have hn4 : n = (n - 4) + 4 := by omega
    rw [hn4, pow_add]
    norm_num
    omega
  rw [hpow] at hupper
  omega

#print axioms six_point_weight_lower_of_one_min_exception
#print axioms no_six_point_partition_with_one_min_exception

end JSP000404Research
