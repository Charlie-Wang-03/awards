import JSP000404Research.SharpTopTailTwoMultiplicity
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Actual planar five-centre top/second-layer, no third-layer subcase

This file closes a previously residual subcase containing a genuine
next-to-top exponent n-2 centre. In configurations with at least four
original centres, the existing geometric top-two-tail theorem guarantees
that no third centre has exponent n-1 or n-2. Under the separately
stated absence of any n-3 exponent *off the chosen top and next centre*,
the remaining (at most three) exponents are at most n-4.

The resulting 8+4+3 <= 16 dyadic budget does not use the unrestricted
six-source payment. This does NOT establish the no-third-layer
hypothesis for general planar AngleCap configurations.
-/

namespace JSP000404Research

open scoped BigOperators

/-- An elementary finite dyadic certificate with a top, a distinct
next-layer point, and at most three further low-exponent points. -/
theorem dyadic_capacity_of_top_next_three_low
    {V : Type*} [Fintype V]
    (k : V → ℕ) (n : ℕ) (s a : V)
    (hn : 4 ≤ n)
    (hcard : Fintype.card V ≤ 5)
    (hsa : s ≠ a)
    (hs : k s = n - 1)
    (ha : k a = n - 2)
    (hother : ∀ i : V, i ≠ s → i ≠ a → k i ≤ n - 4) :
    (∑ i : V, 2 ^ k i) ≤ 2 ^ n := by
  classical
  let S : Finset V := ((Finset.univ : Finset V).erase s).erase a
  have haNot : a ∉ S := by simp [S]
  have hsNot : s ∉ insert a S := by simp [S, hsa]
  have hUniv : insert s (insert a S) = (Finset.univ : Finset V) := by
    ext i
    simp [S]
    tauto
  have hcount : S.card ≤ 3 := by
    have hh : (insert s (insert a S)).card = S.card + 2 := by
      simp [hsNot, haNot]
    rw [hUniv, Finset.card_univ] at hh
    omega
  have hrest : (∑ i ∈ S, 2 ^ k i) ≤ S.card * 2 ^ (n - 4) := by
    calc
      (∑ i ∈ S, 2 ^ k i) ≤ ∑ i ∈ S, 2 ^ (n - 4) := by
        apply Finset.sum_le_sum
        intro i hi
        have his : i ≠ s := by
          intro h
          subst i
          have hsNot : s ∉ S := by simp [S]
          exact hsNot hi
        have hia : i ≠ a := by
          intro h
          subst i
          exact haNot hi
        exact Nat.pow_le_pow_right (by decide : 0 < 2) (hother i his hia)
      _ = S.card * 2 ^ (n - 4) := by simp
  have hrest3 : (∑ i ∈ S, 2 ^ k i) ≤ 3 * 2 ^ (n - 4) :=
    hrest.trans (Nat.mul_le_mul_right _ hcount)
  have hsum :
      (∑ i : V, 2 ^ k i) =
        2 ^ (n - 1) + 2 ^ (n - 2) + (∑ i ∈ S, 2 ^ k i) := by
    rw [← hUniv, Finset.sum_insert hsNot, Finset.sum_insert haNot, hs, ha]
    omega
  have htopPow : 2 ^ (n - 1) = 8 * 2 ^ (n - 4) := by
    calc
      2 ^ (n - 1) = 2 ^ ((n - 4) + 3) := by congr 1 <;> omega
      _ = 8 * 2 ^ (n - 4) := by rw [pow_add]; norm_num [mul_comm]
  have hnextPow : 2 ^ (n - 2) = 4 * 2 ^ (n - 4) := by
    calc
      2 ^ (n - 2) = 2 ^ ((n - 4) + 2) := by congr 1 <;> omega
      _ = 4 * 2 ^ (n - 4) := by rw [pow_add]; norm_num [mul_comm]
  have hbudget : 2 ^ n = 16 * 2 ^ (n - 4) := by
    calc
      2 ^ n = 2 ^ ((n - 4) + 4) := by congr 1 <;> omega
      _ = 16 * 2 ^ (n - 4) := by rw [pow_add]; norm_num [mul_comm]
  rw [hsum, htopPow, hnextPow, hbudget]
  omega

/-- A genuine planar AngleCap subcase with a REAL n-2 exponent centre.

Only the no-third-layer condition is assumed. The exclusion of other
n-1 and n-2 centres follows from the already proved arbitrary-four-plus
planar geometric top-two-tail theorem. -/
theorem planar_five_centre_top_next_no_third_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard4 : 4 ≤ Fintype.card V)
    (hcard5 : Fintype.card V ≤ 5)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s a : V)
    (hsa : s ≠ a)
    (hs : centreExponent (C s) t = n - 1)
    (ha : centreExponent (C a) t = n - 2)
    (hnoThird : ∀ i : V, i ≠ s → i ≠ a →
      centreExponent (C i) t ≠ n - 3) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  classical
  let k : V → ℕ := fun i => centreExponent (C i) t
  let T : Finset V :=
    (Finset.univ : Finset V).filter (fun i => n - 3 < k i)
  have hTcard : T.card ≤ 2 := by
    exact topTwo_tailCount_le_two_of_card_ge_four
      hp hcap hcard4 (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam C s hs
  have hsT : s ∈ T := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [k]
    rw [hs]
    omega
  have haT : a ∈ T := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [k]
    rw [ha]
    omega
  have hsub : ({s, a} : Finset V) ⊆ T := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hsT
    · exact haT
  have hpaircard : ({s, a} : Finset V).card = 2 :=
    Finset.card_pair hsa
  have hTeq : T = ({s, a} : Finset V) := by
    exact Finset.eq_of_subset_of_card_le hsub
      (by simpa [hpaircard] using hTcard)
  have hother :
      ∀ i : V, i ≠ s → i ≠ a → k i ≤ n - 4 := by
    intro i his hia
    have hle : k i ≤ n - 3 := by
      by_contra hbad
      have hiT : i ∈ T := by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have hiPair : i ∈ ({s, a} : Finset V) := by
        simpa [hTeq] using hiT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiPair
      exact hiPair.elim his hia
    have hneq : k i ≠ n - 3 := hnoThird i his hia
    omega
  exact dyadic_capacity_of_top_next_three_low
    k n s a hn hcard5 hsa hs ha hother

#print axioms dyadic_capacity_of_top_next_three_low
#print axioms planar_five_centre_top_next_no_third_capacity

end JSP000404Research
