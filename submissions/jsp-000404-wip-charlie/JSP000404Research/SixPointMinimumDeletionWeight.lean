import JSP000404Research.ConcreteCentreDeletionMonotone
import Mathlib.Tactic

/-!
# One survivor gain compensates deletion of one six-point minimum

In the six-point terminal profile

  exponent(top) = n-1,
  exponent(v)   = n-3 for every v != top,

deleting any non-top minimum removes dyadic mass 2^(n-3).

Deletion is exponent-monotone at every surviving centre.  Therefore, if one
other surviving minimum gains one exponent unit, its dyadic mass increases from

  2^(n-3) to at least 2^(n-2),

which adds exactly one extra copy of 2^(n-3).  This completely compensates the
deleted minimum.

This is the non-top analogue of SixPointTopDeletionWeight, but it needs only
one gain rather than four.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Pure finite weight ledger: one unit gain among the five survivors
compensates deleting one minimum from the 1+5 six-point profile. -/
theorem five_survivor_weight_ge_six_point_profile_of_one_minimum_gain
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ}
    (hn : 3 ≤ n)
    (top deleted gain : V)
    (hcard : Fintype.card V = 6)
    (hdelTop : deleted ≠ top)
    (hgainDel : gain ≠ deleted)
    (hgainTop : gain ≠ top)
    (childExponent : V → ℕ)
    (hTop :
      n - 1 ≤ childExponent top)
    (hbase :
      ∀ v : V, v ≠ deleted → v ≠ top →
        n - 3 ≤ childExponent v)
    (hgain :
      n - 2 ≤ childExponent gain) :
    2 ^ (n - 1) + 5 * 2 ^ (n - 3)
      ≤
    ∑ v ∈ (Finset.univ.erase deleted : Finset V),
      2 ^ childExponent v := by
  classical
  let S : Finset V := Finset.univ.erase deleted
  let R : Finset V := (S.erase top).erase gain

  have htopS : top ∈ S := by
    simp [S, hdelTop]
  have hgainS : gain ∈ S := by
    simp [S, hgainDel]
  have hgainST :
      gain ∈ S.erase top := by
    simp [S, hgainDel, hgainTop]

  have hScard : S.card = 5 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ deleted),
        Finset.card_univ, hcard]

  have hRcard : R.card = 3 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem hgainST,
        Finset.card_erase_of_mem htopS,
        hScard]

  have htopLower :
      2 ^ (n - 1) ≤ 2 ^ childExponent top :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hTop

  have hgainLower :
      2 ^ (n - 2) ≤ 2 ^ childExponent gain :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hgain

  have hrestLower :
      3 * 2 ^ (n - 3) ≤
        ∑ v ∈ R, 2 ^ childExponent v := by
    calc
      3 * 2 ^ (n - 3)
          = ∑ _v ∈ R, 2 ^ (n - 3) := by
              simp [hRcard, Nat.mul_comm]
      _ ≤ ∑ v ∈ R, 2 ^ childExponent v := by
            exact Finset.sum_le_sum
              (fun v hv => by
                apply Nat.pow_le_pow_right
                  (by norm_num : 0 < 2)
                apply hbase v
                · have hvS :
                    v ∈ S := by
                    have h := (Finset.mem_erase.mp
                      (Finset.mem_erase.mp hv).2).2
                    exact h
                  simpa [S] using hvS
                · exact
                    (Finset.mem_erase.mp
                      (Finset.mem_erase.mp hv).2).1)

  have hsplit :
      (∑ v ∈ S, 2 ^ childExponent v)
        =
      2 ^ childExponent top +
      2 ^ childExponent gain +
      ∑ v ∈ R, 2 ^ childExponent v := by
    have h1 :=
      Finset.sum_erase_add
        (s := S)
        (f := fun v => 2 ^ childExponent v)
        htopS
    have h2 :=
      Finset.sum_erase_add
        (s := S.erase top)
        (f := fun v => 2 ^ childExponent v)
        hgainST
    dsimp [R]
    omega

  have hchild :
      2 ^ (n - 1) +
          2 ^ (n - 2) +
          3 * 2 ^ (n - 3)
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

/-- Concrete centre-exponent version.  If deleting one minimum gives a unit
gain at any other minimum, the deletion post-weight dominates the original
six-point dyadic weight. -/
theorem six_point_minimum_deletion_compensated_of_one_gain
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} {hp : Function.Injective p}
    {t : ℝ} {n : ℕ}
    (hcard : Fintype.card V = 6)
    (hn : 3 ≤ n)
    (ht0 : 0 ≤ t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (top deleted gain : V)
    (hdelTop : deleted ≠ top)
    (hgainDel : gain ≠ deleted)
    (hgainTop : gain ≠ top)
    (hTop :
      centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hgain :
      centreExponent (C gain) t + 1 ≤
        concreteDeletionAfter C
          (by omega : 3 ≤ Fintype.card V)
          t deleted gain) :
    2 ^ (n - 1) + 5 * 2 ^ (n - 3)
      ≤
    deletionPostWeight
      (concreteDeletionAfter C
        (by omega : 3 ≤ Fintype.card V) t)
      deleted := by
  let hV : 3 ≤ Fintype.card V := by omega
  let childExponent : V → ℕ :=
    fun v =>
      if hv : v = deleted then 0
      else concreteDeletionAfter C hV t deleted v

  have hTopChild :
      n - 1 ≤ childExponent top := by
    have hmono :=
      concreteDeletionAfter_mono
        C hV ht0 (by exact hdelTop.symm)
    rw [hTop] at hmono
    simpa [childExponent, hdelTop.symm] using hmono

  have hbase :
      ∀ v : V, v ≠ deleted → v ≠ top →
        n - 3 ≤ childExponent v := by
    intro v hvd hvt
    have hmono :=
      concreteDeletionAfter_mono C hV ht0 hvd
    rw [hMin v hvt] at hmono
    simpa [childExponent, hvd] using hmono

  have hgainChild :
      n - 2 ≤ childExponent gain := by
    have hminGain := hMin gain hgainTop
    have hg :
        n - 3 + 1 ≤
          concreteDeletionAfter C hV t deleted gain := by
      rw [← hminGain]
      exact hgain
    have hsub : n - 3 + 1 = n - 2 := by omega
    rw [hsub] at hg
    simpa [childExponent, hgainDel] using hg

  have hledger :=
    five_survivor_weight_ge_six_point_profile_of_one_minimum_gain
      hn top deleted gain hcard
      hdelTop hgainDel hgainTop
      childExponent hTopChild hbase hgainChild

  unfold deletionPostWeight
  have hsumEq :
      (∑ v ∈ (Finset.univ.erase deleted : Finset V),
          2 ^ childExponent v)
        =
      ∑ v ∈ (Finset.univ.erase deleted : Finset V),
          2 ^ concreteDeletionAfter C hV t deleted v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hvd : v ≠ deleted :=
      (Finset.mem_erase.mp hv).1
    simp [childExponent, hvd]
  rw [hsumEq] at hledger
  exact hledger

#print axioms five_survivor_weight_ge_six_point_profile_of_one_minimum_gain
#print axioms six_point_minimum_deletion_compensated_of_one_gain

end JSP000404Research
