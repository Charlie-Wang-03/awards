import JSP000404Research.SevenCentreTopThirdSupportOneCapacity
import Mathlib.Tactic

/-!
# A fourth dyadic scale closes selected NINE-centre true geometric profiles

For n >= 5, the genuine exponent upper bound forces k(i) <= n-1.
Write m for cardinal V and r_j for the number of original centres with
exponent n-j (j=1,2,3,4).  Every other centre has k(i) <= n-5.
Then the exact dyadic cardinal budget is

  sum_i 2^k(i) <= (m + 15*r₁ + 7*r₂ + 3*r₃ + r₄) * 2^(n-5).

The weighted census criterion <=32 proves capacity for ANY finite V.

For nine original centres, a genuine top n-1, no n-2 centres,
ALL n-3 centres of quotient support one, and at most five n-4 centres,
the earlier TRUE planar geometric top/third support-one exclusion
proves r₁=1, r₂=0, r₃<=1. The budget is <=9+15+0+3+5=32.
The n-4 multiplicity premise is an explicit additional assumption,
NOT proved universally for all AngleCap configurations.

The global six-source actual external TRUE-hole payment is not used.
-/

namespace JSP000404Research

open scoped BigOperators

theorem dyadic_capacity_of_four_layer_count_tradeoff
    {V : Type*} [Fintype V]
    (k : V → ℕ) (n : ℕ)
    (hn : 5 ≤ n)
    (hmax : ∀ i : V, k i ≤ n - 1)
    (htrade : Fintype.card V +
      15 * ((Finset.univ : Finset V).filter (fun i => k i = n - 1)).card +
      7 * ((Finset.univ : Finset V).filter (fun i => k i = n - 2)).card +
      3 * ((Finset.univ : Finset V).filter (fun i => k i = n - 3)).card +
      ((Finset.univ : Finset V).filter (fun i => k i = n - 4)).card ≤ 32) :
    (∑ i : V, 2 ^ k i) ≤ 2 ^ n := by
  classical
  let H : Finset V := (Finset.univ : Finset V).filter (fun i => k i = n - 1)
  let N : Finset V := (Finset.univ : Finset V).filter (fun i => k i = n - 2)
  let T : Finset V := (Finset.univ : Finset V).filter (fun i => k i = n - 3)
  let F : Finset V := (Finset.univ : Finset V).filter (fun i => k i = n - 4)
  let B : ℕ := 2 ^ (n - 5)
  have htop : 2 ^ (n - 1) = 16 * B := by
    dsimp [B]
    conv_lhs => rw [show n - 1 = (n - 5) + 4 by omega, pow_add]
    norm_num [mul_comm]
  have hnext : 2 ^ (n - 2) = 8 * B := by
    dsimp [B]
    conv_lhs => rw [show n - 2 = (n - 5) + 3 by omega, pow_add]
    norm_num [mul_comm]
  have hthird : 2 ^ (n - 3) = 4 * B := by
    dsimp [B]
    conv_lhs => rw [show n - 3 = (n - 5) + 2 by omega, pow_add]
    norm_num [mul_comm]
  have hfourth : 2 ^ (n - 4) = 2 * B := by
    dsimp [B]
    conv_lhs => rw [show n - 4 = (n - 5) + 1 by omega, pow_add]
    norm_num [mul_comm]
  have hpoint : ∀ i : V,
      2 ^ k i ≤ B +
        (if k i = n - 1 then 15 * B else 0) +
        (if k i = n - 2 then 7 * B else 0) +
        (if k i = n - 3 then 3 * B else 0) +
        (if k i = n - 4 then B else 0) := by
    intro i
    by_cases hiH : k i = n - 1
    · have hiN : k i ≠ n - 2 := by omega
      have hiT : k i ≠ n - 3 := by omega
      have hiF : k i ≠ n - 4 := by omega
      simp only [if_pos hiH, if_neg hiN, if_neg hiT, if_neg hiF, add_zero]
      rw [hiH, htop]
      omega
    · by_cases hiN : k i = n - 2
      · have hiT : k i ≠ n - 3 := by omega
        have hiF : k i ≠ n - 4 := by omega
        simp only [if_neg hiH, if_pos hiN, if_neg hiT, if_neg hiF, add_zero]
        rw [hiN, hnext]
        omega
      · by_cases hiT : k i = n - 3
        · have hiF : k i ≠ n - 4 := by omega
          simp only [if_neg hiH, if_neg hiN, if_pos hiT, if_neg hiF, add_zero]
          rw [hiT, hthird]
          omega
        · by_cases hiF : k i = n - 4
          · simp only [if_neg hiH, if_neg hiN, if_neg hiT, if_pos hiF, add_zero]
            rw [hiF, hfourth]
            omega
          · have hlo : k i ≤ n - 5 := by
              have he := hmax i
              omega
            simp only [if_neg hiH, if_neg hiN, if_neg hiT, if_neg hiF, add_zero]
            exact Nat.pow_le_pow_right (by decide : 0 < 2) hlo
  have hsumBound :
      (∑ i : V, 2 ^ k i) ≤
        ∑ i : V, (B +
          (if k i = n - 1 then 15 * B else 0) +
          (if k i = n - 2 then 7 * B else 0) +
          (if k i = n - 3 then 3 * B else 0) +
          (if k i = n - 4 then B else 0)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpoint i
  have hH :
      (∑ i : V, if k i = n - 1 then 15 * B else 0) =
        H.card * (15 * B) := by
    simp [H, Finset.sum_ite]
  have hN :
      (∑ i : V, if k i = n - 2 then 7 * B else 0) =
        N.card * (7 * B) := by
    simp [N, Finset.sum_ite]
  have hT :
      (∑ i : V, if k i = n - 3 then 3 * B else 0) =
        T.card * (3 * B) := by
    simp [T, Finset.sum_ite]
  have hF :
      (∑ i : V, if k i = n - 4 then B else 0) =
        F.card * B := by
    simp [F, Finset.sum_ite]
  have hsumEq :
      (∑ i : V, (B +
          (if k i = n - 1 then 15 * B else 0) +
          (if k i = n - 2 then 7 * B else 0) +
          (if k i = n - 3 then 3 * B else 0) +
          (if k i = n - 4 then B else 0))) =
        (Fintype.card V + 15 * H.card + 7 * N.card +
          3 * T.card + F.card) * B := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib, hH, hN, hT, hF]
    simp [add_mul, mul_assoc, mul_left_comm, mul_comm]
    ring
  have hbudget : 32 * B = 2 ^ n := by
    dsimp [B]
    calc
      32 * 2 ^ (n - 5) = 2 ^ 5 * 2 ^ (n - 5) := by norm_num
      _ = 2 ^ (5 + (n - 5)) := by rw [← pow_add]
      _ = 2 ^ n := by congr 1 <;> omega
  calc
    (∑ i : V, 2 ^ k i) ≤
        ∑ i : V, (B +
          (if k i = n - 1 then 15 * B else 0) +
          (if k i = n - 2 then 7 * B else 0) +
          (if k i = n - 3 then 3 * B else 0) +
          (if k i = n - 4 then B else 0)) := hsumBound
    _ = (Fintype.card V + 15 * H.card + 7 * N.card +
          3 * T.card + F.card) * B := hsumEq
    _ ≤ 32 * B := Nat.mul_le_mul_right _ (by simpa [H,N,T,F] using htrade)
    _ = 2 ^ n := hbudget

theorem planar_nine_centre_top_no_next_third_support_one_fourth_at_most_five
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard3 : 3 ≤ Fintype.card V)
    (hcard9 : Fintype.card V ≤ 9)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s : V)
    (hs : centreExponent (C s) t = n - 1)
    (hnoNext : ∀ i : V, centreExponent (C i) t ≠ n - 2)
    (hThirdSupportOne : ∀ i : V,
      centreExponent (C i) t = n - 3 →
      positiveSupport (centreQuotient (C i) t) = 1)
    (hFourthCard :
      ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 4)).card ≤ 5) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  classical
  let k : V → ℕ := fun i => centreExponent (C i) t
  let H : Finset V := (Finset.univ : Finset V).filter (fun i => k i = n - 1)
  let N : Finset V := (Finset.univ : Finset V).filter (fun i => k i = n - 2)
  let T : Finset V := (Finset.univ : Finset V).filter (fun i => k i = n - 3)
  let F : Finset V := (Finset.univ : Finset V).filter (fun i => k i = n - 4)
  have htopEq : H = {s} := by
    ext i
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hi
      exact topExponent_eq_fixed_top hp hcap hcard3
        (by omega : 3 ≤ n) hdelta0 hdeltaHalf ht hlam C s i hs hi
    · intro hi
      subst i
      exact hs
  have htopCard : H.card = 1 := by simp [htopEq]
  have hnextCard : N.card = 0 := by simp [N, k, hnoNext]
  have hthirdCard : T.card ≤ 1 := by
    have hsub : T ⊆
        (Finset.univ : Finset V).filter
          (fun i => i ≠ s ∧
            centreExponent (C i) t = n - 3 ∧
            positiveSupport (centreQuotient (C i) t) = 1) := by
      intro i hi
      have hk : centreExponent (C i) t = n - 3 :=
        (Finset.mem_filter.mp hi).2
      have his : i ≠ s := by
        intro he
        subst i
        omega
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, ⟨his, hk, hThirdSupportOne i hk⟩⟩
    exact (Finset.card_le_card hsub).trans
      (top_third_support_one_count_le_one_n_ge_five
        hp hcap hn hdelta0 hdeltaHalf ht hlam C s hs)
  have hdelta1 : delta < 1 := by linarith
  have hmax : ∀ i : V, k i ≤ n - 1 := by
    intro i
    change centreExponent (C i) t ≤ n - 1
    have hlt : centreExponent (C i) t < n :=
      centreExponent_lt_n (C i) n delta t
        (by omega : 1 ≤ n) hdelta0 hdelta1 ht
    omega
  have htrade :
      Fintype.card V + 15 * H.card + 7 * N.card +
        3 * T.card + F.card ≤ 32 := by
    have hfifth : F.card ≤ 5 := by simpa only [F,k] using hFourthCard
    omega
  exact dyadic_capacity_of_four_layer_count_tradeoff k n hn hmax
    (by simpa only [H,N,T,F,k] using htrade)

#print axioms dyadic_capacity_of_four_layer_count_tradeoff
#print axioms planar_nine_centre_top_no_next_third_support_one_fourth_at_most_five

end JSP000404Research
