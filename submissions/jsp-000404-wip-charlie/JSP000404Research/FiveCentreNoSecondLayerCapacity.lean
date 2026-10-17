import JSP000404Research.TopTwoTailMultiplicity
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Genuine five-centre no-second-layer lower-branch capacity

The global six-source packing/payment theorem is not used here.
An elementary dyadic budget closes the true five-centre geometric
subcase with one exponent n-1 and no exponent n-2.
The absence of the second layer is a REAL extra assumption;
the arbitrary five-centre case remains open in this module.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Pure arithmetic: a top contribution 2^(n-1) and at most four
contributions bounded by 2^(n-3) fit in the capacity 2^n. -/
theorem dyadic_capacity_of_top_and_four_low
    {V : Type*} [Fintype V]
    (k : V → ℕ) (n : ℕ) (s : V)
    (hn : 3 ≤ n)
    (hcard : Fintype.card V ≤ 5)
    (htop : k s = n - 1)
    (hother : ∀ i : V, i ≠ s → k i ≤ n - 3) :
    (∑ i : V, 2 ^ k i) ≤ 2 ^ n := by
  classical
  let S : Finset V := (Finset.univ : Finset V).erase s
  have hsnot : s ∉ S := by simp [S]
  have huniv : insert s S = (Finset.univ : Finset V) := by
    simp [S]
  have hcardS : S.card ≤ 4 := by
    have h := Finset.card_insert_of_not_mem hsnot
    rw [huniv, Finset.card_univ] at h
    omega
  have hlow : (∑ i ∈ S, 2 ^ k i) ≤ S.card * 2 ^ (n - 3) := by
    calc
      (∑ i ∈ S, 2 ^ k i) ≤ ∑ i ∈ S, 2 ^ (n - 3) := by
        apply Finset.sum_le_sum
        intro i hi
        have his : i ≠ s := by
          intro his
          subst i
          exact hsnot hi
        exact Nat.pow_le_pow_right (by decide : 0 < 2) (hother i his)
      _ = S.card * 2 ^ (n - 3) := by simp [mul_comm]
  have hlow4 : (∑ i ∈ S, 2 ^ k i) ≤ 4 * 2 ^ (n - 3) := by
    exact hlow.trans (Nat.mul_le_mul_right _ hcardS)
  have hsum :
      (∑ i : V, 2 ^ k i) =
        2 ^ (n - 1) + ∑ i ∈ S, 2 ^ k i := by
    rw [← huniv, Finset.sum_insert hsnot, htop]
  have htopPow : 2 ^ (n - 1) = 4 * 2 ^ (n - 3) := by
    calc
      2 ^ (n - 1) = 2 ^ ((n - 3) + 2) := by congr 1 <;> omega
      _ = 4 * 2 ^ (n - 3) := by rw [pow_add]; norm_num [mul_comm]
  have htargetPow : 2 ^ n = 8 * 2 ^ (n - 3) := by
    calc
      2 ^ n = 2 ^ ((n - 3) + 3) := by congr 1 <;> omega
      _ = 8 * 2 ^ (n - 3) := by rw [pow_add]; norm_num [mul_comm]
  rw [hsum, htopPow, htargetPow]
  omega

/-- A real planar AngleCap subcase, not merely a profile assumption:
at most five original centres, one actual n-1 centre, and no n-2
centres imply the original lower-branch dyadic capacity. -/
theorem planar_five_centre_no_second_layer_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard3 : 3 ≤ Fintype.card V)
    (hcard5 : Fintype.card V ≤ 5)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s : V)
    (hs : centreExponent (C s) t = n - 1)
    (hnoSecond : ∀ i : V, centreExponent (C i) t ≠ n - 2) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  have hdelta1 : delta < 1 := by linarith
  have hother :
      ∀ i : V, i ≠ s → centreExponent (C i) t ≤ n - 3 := by
    intro i his
    have hiLt : centreExponent (C i) t < n :=
      centreExponent_lt_n (C i) n delta t
        (by omega : 1 ≤ n) hdelta0 hdelta1 ht
    have hiNotTop : centreExponent (C i) t ≠ n - 1 := by
      intro hiTop
      have hieq := topExponent_eq_fixed_top hp hcap hcard3 hn
        hdelta0 hdeltaHalf ht hlam C s i hs hiTop
      exact his hieq
    have hiNotSecond := hnoSecond i
    omega
  exact dyadic_capacity_of_top_and_four_low
    (fun i => centreExponent (C i) t) n s hn hcard5 hs hother

#print axioms dyadic_capacity_of_top_and_four_low
#print axioms planar_five_centre_no_second_layer_capacity

end JSP000404Research
