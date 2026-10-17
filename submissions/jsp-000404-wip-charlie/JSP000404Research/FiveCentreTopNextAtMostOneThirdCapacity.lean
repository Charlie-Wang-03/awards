import JSP000404Research.FiveCentreTopNextNoThirdCapacity
import Mathlib.Tactic

/-!
# Five-centre top/next dyadic budget with at most ONE third-layer centre

The previous actual geometric theorem covers ZERO third-layer centres.
Here the allowance is extended to at most ONE third-layer centre among
the vertices other than the fixed n-1 and n-2 centres.

No assertion is made that AngleCap *automatically* implies this extra
third-layer multiplicity restriction, nor is the global six-source
payment solved.  The extremal budget is sharp: 8+4+2+1+1 = 16.
-/

namespace JSP000404Research

open scoped BigOperators

/-- A sharp elementary dyadic five-centre profile certificate. -/
theorem dyadic_capacity_of_top_next_one_third_two_low
    {V : Type*} [Fintype V]
    (k : V → ℕ) (n : ℕ) (s a b : V)
    (hn : 4 ≤ n)
    (hcard : Fintype.card V ≤ 5)
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (hs : k s = n - 1)
    (ha : k a = n - 2)
    (hb : k b ≤ n - 3)
    (hother : ∀ i : V, i ≠ s → i ≠ a → i ≠ b → k i ≤ n - 4) :
    (∑ i : V, 2 ^ k i) ≤ 2 ^ n := by
  classical
  let S : Finset V := (((Finset.univ : Finset V).erase s).erase a).erase b
  have hbNot : b ∉ S := by simp [S]
  have haNot : a ∉ insert b S := by simp [S, hab]
  have hsNot : s ∉ insert a (insert b S) := by simp [S, hsa, hsb]
  have hUniv : insert s (insert a (insert b S)) =
      (Finset.univ : Finset V) := by
    ext i
    simp [S]
    tauto
  have hcount : S.card ≤ 2 := by
    have hh : (insert s (insert a (insert b S))).card = S.card + 3 := by
      simp [hsNot, haNot, hbNot]
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
          have hnot : s ∉ S := by simp [S]
          exact hnot hi
        have hia : i ≠ a := by
          intro h
          subst i
          have hnot : a ∉ S := by simp [S]
          exact hnot hi
        have hib : i ≠ b := by
          intro h
          subst i
          exact hbNot hi
        exact Nat.pow_le_pow_right (by decide : 0 < 2) (hother i his hia hib)
      _ = S.card * 2 ^ (n - 4) := by simp
  have hrest2 : (∑ i ∈ S, 2 ^ k i) ≤ 2 * 2 ^ (n - 4) :=
    hrest.trans (Nat.mul_le_mul_right _ hcount)
  have hsum : (∑ i : V, 2 ^ k i) =
      2 ^ (n - 1) + 2 ^ (n - 2) + 2 ^ k b + (∑ i ∈ S, 2 ^ k i) := by
    rw [← hUniv, Finset.sum_insert hsNot, Finset.sum_insert haNot,
      Finset.sum_insert hbNot, hs, ha]
    omega
  have hbPow : 2 ^ k b ≤ 2 * 2 ^ (n - 4) := by
    calc
      2 ^ k b ≤ 2 ^ (n - 3) := Nat.pow_le_pow_right (by decide : 0 < 2) hb
      _ = 2 * 2 ^ (n - 4) := by
        conv_lhs => rw [show n - 3 = (n - 4) + 1 by omega, pow_add]
        norm_num [mul_comm]
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

/-- Actual AngleCap top/next, with an extra hypothesis that distinct
remaining third-layer centres cannot coexist.  Top-two-tail rigidity,
including the uniqueness of top/next layers, is DERIVED from geometry. -/
theorem planar_five_centre_top_next_at_most_one_third_capacity
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
    (hthirdUnique : ∀ i j : V, i ≠ s → i ≠ a →
      j ≠ s → j ≠ a →
      centreExponent (C i) t = n - 3 →
      centreExponent (C j) t = n - 3 → i = j) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  classical
  let k : V → ℕ := fun i => centreExponent (C i) t
  let T : Finset V :=
    (Finset.univ : Finset V).filter (fun i => n - 3 < k i)
  have hTcard : T.card ≤ 2 :=
    topTwo_tailCount_le_two_of_card_ge_four
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
  have hTeq : T = ({s, a} : Finset V) := by
    symm
    exact Finset.eq_of_subset_of_card_le hsub
      (by simpa [Finset.card_pair hsa] using hTcard)
  have hle : ∀ i : V, i ≠ s → i ≠ a → k i ≤ n - 3 := by
    intro i his hia
    by_contra hbad
    have hiT : i ∈ T := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hp : i ∈ ({s, a} : Finset V) := by
      simpa [hTeq] using hiT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    exact hp.elim his hia
  by_cases hthird : ∃ b : V, b ≠ s ∧ b ≠ a ∧ k b = n - 3
  · rcases hthird with ⟨b, hbs, hba, hb⟩
    have hother :
        ∀ i : V, i ≠ s → i ≠ a → i ≠ b → k i ≤ n - 4 := by
      intro i his hia hib
      have he : k i ≤ n - 3 := hle i his hia
      have hneq : k i ≠ n - 3 := by
        intro hi
        have hieq : i = b :=
          hthirdUnique i b his hia hbs hba hi hb
        exact hib hieq
      omega
    exact dyadic_capacity_of_top_next_one_third_two_low
      k n s a b hn hcard5 hsa hbs.symm hba.symm hs ha
        (by simpa [k] using (Nat.le_of_eq hb)) hother
  · have hnoThird : ∀ i : V, i ≠ s → i ≠ a → k i ≠ n - 3 := by
      intro i his hia hi
      exact hthird ⟨i, his, hia, hi⟩
    exact dyadic_capacity_of_top_next_three_low
      k n s a hn hcard5 hsa hs ha
        (by
          intro i his hia
          have he := hle i his hia
          have hneq := hnoThird i his hia
          omega)

#print axioms dyadic_capacity_of_top_next_one_third_two_low
#print axioms planar_five_centre_top_next_at_most_one_third_capacity

end JSP000404Research
