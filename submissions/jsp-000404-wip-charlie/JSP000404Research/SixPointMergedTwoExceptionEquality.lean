import JSP000404Research.BinaryEdgePartition
import JSP000404Research.WeightedHanselEquality
import Mathlib.Tactic

/-!
# Six-point equality terminal with two exceptional minima

For the merged six-point profile, allowing two non-top minima one extra active
colour gives exactly the Boolean-cube capacity:

  top:      active <= 1  contributes >= 2^(n-1),
  two bad:  active <= 4  contribute 2 * 2^(n-4),
  three others:
            active <= 3  contribute 3 * 2^(n-3).

The sum is exactly 2^n.

Therefore any BinaryEdgePartition satisfying these local bounds must attain
equality in weighted Hansel.  The completed partial Boolean cubes are not just
disjoint: they bijectively tile the whole n-cube.

This is the rigidity interface for the remaining "exactly two bad minima"
phase branch.
-/

namespace JSP000404Research

open scoped BigOperators
open BinaryEdgePartition

theorem six_point_two_min_exceptions_weight_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (hn : 4 ≤ n)
    (P : BinaryEdgePartition V n)
    (top bad₁ bad₂ : V)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hTop : (active P top).card ≤ 1)
    (hBad₁ : (active P bad₁).card ≤ 4)
    (hBad₂ : (active P bad₂).card ≤ 4)
    (hOther :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        (active P v).card ≤ 3) :
    (∑ v : V, 2 ^ (n - (active P v).card)) = 2 ^ n := by
  classical
  let S : Finset V :=
    ((Finset.univ.erase top).erase bad₁).erase bad₂
  have hb₁Mem :
      bad₁ ∈ (Finset.univ.erase top : Finset V) := by
    simp [htb₁]
  have hb₂Mem :
      bad₂ ∈ ((Finset.univ.erase top).erase bad₁ : Finset V) := by
    simp [htb₂, hb₁₂]
  have hScard : S.card = 3 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem hb₂Mem,
        Finset.card_erase_of_mem hb₁Mem,
        Finset.card_erase_of_mem (Finset.mem_univ top)]
    simp [hcard]

  have htopPow :
      2 ^ (n - 1) ≤ 2 ^ (n - (active P top).card) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  have hbad₁Pow :
      2 ^ (n - 4) ≤ 2 ^ (n - (active P bad₁).card) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  have hbad₂Pow :
      2 ^ (n - 4) ≤ 2 ^ (n - (active P bad₂).card) := by
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  have hotherPow :
      ∀ v ∈ S,
        2 ^ (n - 3) ≤ 2 ^ (n - (active P v).card) := by
    intro v hv
    have hv₂ := Finset.mem_erase.mp hv
    have hv₁ := Finset.mem_erase.mp hv₂.2
    have hvt := (Finset.mem_erase.mp hv₁.2).1
    have hvb₁ := hv₁.1
    have hvb₂ := hv₂.1
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    have ha := hOther v hvt hvb₁ hvb₂
    omega
  have hsumS :
      S.card * 2 ^ (n - 3) ≤
        ∑ v ∈ S, 2 ^ (n - (active P v).card) := by
    calc
      S.card * 2 ^ (n - 3)
          = ∑ _v ∈ S, 2 ^ (n - 3) := by
              simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ S, 2 ^ (n - (active P v).card) := by
            exact Finset.sum_le_sum
              (fun v hv => hotherPow v hv)

  have hdecomp :
      (∑ v : V, 2 ^ (n - (active P v).card)) =
        2 ^ (n - (active P top).card) +
        2 ^ (n - (active P bad₁).card) +
        2 ^ (n - (active P bad₂).card) +
        ∑ v ∈ S, 2 ^ (n - (active P v).card) := by
    rw [← Finset.sum_erase_add
      (fun v => 2 ^ (n - (active P v).card))
      (Finset.mem_univ top)]
    rw [← Finset.sum_erase_add
      (fun v => 2 ^ (n - (active P v).card))
      hb₁Mem]
    rw [← Finset.sum_erase_add
      (fun v => 2 ^ (n - (active P v).card))
      hb₂Mem]
    dsimp [S]
    omega

  have hlower :
      2 ^ (n - 1) +
          2 ^ (n - 4) +
          2 ^ (n - 4) +
          3 * 2 ^ (n - 3)
        ≤
      ∑ v : V, 2 ^ (n - (active P v).card) := by
    rw [hdecomp]
    rw [hScard] at hsumS
    omega

  have hn1 : n - 1 = (n - 4) + 3 := by omega
  have hn3 : n - 3 = (n - 4) + 1 := by omega
  have hn4 : n = (n - 4) + 4 := by omega
  have hbase :
      2 ^ (n - 1) +
          2 ^ (n - 4) +
          2 ^ (n - 4) +
          3 * 2 ^ (n - 3)
        =
      2 ^ n := by
    rw [hn1, hn3, hn4, pow_add, pow_add, pow_add]
    norm_num
    ring

  have hlower' :
      2 ^ n ≤
        ∑ v : V, 2 ^ (n - (active P v).card) := by
    rw [← hbase]
    exact hlower
  have hupper := BinaryEdgePartition.weighted_capacity P
  omega

theorem six_point_two_min_exceptions_completeWord_bijective
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (hn : 4 ≤ n)
    (P : BinaryEdgePartition V n)
    (top bad₁ bad₂ : V)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hTop : (active P top).card ≤ 1)
    (hBad₁ : (active P bad₁).card ≤ 4)
    (hBad₂ : (active P bad₂).card ≤ 4)
    (hOther :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        (active P v).card ≤ 3) :
    Function.Bijective
      (fun x : Σ v, FreeCoordinates (active P v) =>
        completeWord P.bit (active P) x.1 x.2) := by
  have hweight :=
    six_point_two_min_exceptions_weight_eq
      hn P top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther
  exact completeWord_sigma_bijective_of_weight_eq
    P.bit (active P) (BinaryEdgePartition.separates P)
    hweight

theorem six_point_two_min_exceptions_every_word_unique
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (hn : 4 ≤ n)
    (P : BinaryEdgePartition V n)
    (top bad₁ bad₂ : V)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hTop : (active P top).card ≤ 1)
    (hBad₁ : (active P bad₁).card ≤ 4)
    (hBad₂ : (active P bad₂).card ≤ 4)
    (hOther :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        (active P v).card ≤ 3)
    (word : Fin n → Bool) :
    ∃! x : Σ v, FreeCoordinates (active P v),
      completeWord P.bit (active P) x.1 x.2 = word := by
  have hweight :=
    six_point_two_min_exceptions_weight_eq
      hn P top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther
  exact existsUnique_completion_of_weight_eq
    P.bit (active P) (BinaryEdgePartition.separates P)
    hweight word

#print axioms six_point_two_min_exceptions_weight_eq
#print axioms six_point_two_min_exceptions_completeWord_bijective
#print axioms six_point_two_min_exceptions_every_word_unique

end JSP000404Research
