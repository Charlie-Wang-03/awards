import JSP000404Research.CentreExponentBounds
import JSP000404Research.ConcreteSharpCentre
import Mathlib.Tactic

/-!
# Three-centre fixed-parameter terminal capacity

For three actual centres at one fixed lower-branch Sendov parameter:

* every concrete exponent is < n;
* an exponent n-1 centre is geometrically SharpAt;
* two sharp centres together with the third point contradict the global angle
  cap when delta<1/2.

Hence at most one of the three exponents equals n-1.  The other two are at
most n-2, so the dyadic mass is bounded by

  2^(n-1) + 2*2^(n-2) = 2^n.

This is a genuine fixed-t terminal theorem and does not re-normalize the
three-point subset.
-/

namespace JSP000404Research

open scoped BigOperators

theorem top_plus_two_next_dyadic_eq
    {n : ℕ} (hn : 2 ≤ n) :
    2 ^ (n - 1) + 2 ^ (n - 2) + 2 ^ (n - 2) = 2 ^ n := by
  let m := n - 2
  have hnm : n = m + 2 := by
    dsimp [m]
    omega
  rw [hnm]
  simp [pow_succ]
  ring

theorem three_dyadic_terms_le_of_at_most_one_top
    {n k0 k1 k2 : ℕ}
    (hn : 2 ≤ n)
    (hk0 : k0 < n) (hk1 : k1 < n) (hk2 : k2 < n)
    (h01 : ¬ (k0 = n - 1 ∧ k1 = n - 1))
    (h02 : ¬ (k0 = n - 1 ∧ k2 = n - 1))
    (h12 : ¬ (k1 = n - 1 ∧ k2 = n - 1)) :
    2 ^ k0 + 2 ^ k1 + 2 ^ k2 ≤ 2 ^ n := by
  have hpow :
      ∀ {a b : ℕ}, a ≤ b → 2 ^ a ≤ 2 ^ b := by
    intro a b hab
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hab
  by_cases h0 : k0 = n - 1
  · have h1not : k1 ≠ n - 1 := by
      intro h1
      exact h01 ⟨h0, h1⟩
    have h2not : k2 ≠ n - 1 := by
      intro h2
      exact h02 ⟨h0, h2⟩
    have hk1' : k1 ≤ n - 2 := by omega
    have hk2' : k2 ≤ n - 2 := by omega
    rw [h0]
    calc
      2 ^ (n - 1) + 2 ^ k1 + 2 ^ k2
          ≤ 2 ^ (n - 1) + 2 ^ (n - 2) + 2 ^ (n - 2) := by
            omega
      _ = 2 ^ n := top_plus_two_next_dyadic_eq hn
  · by_cases h1 : k1 = n - 1
    · have h2not : k2 ≠ n - 1 := by
        intro h2
        exact h12 ⟨h1, h2⟩
      have hk0' : k0 ≤ n - 2 := by omega
      have hk2' : k2 ≤ n - 2 := by omega
      have hp0 := hpow hk0'
      have hp2 := hpow hk2'
      rw [h1]
      calc
        2 ^ k0 + 2 ^ (n - 1) + 2 ^ k2
            ≤ 2 ^ (n - 2) + 2 ^ (n - 1) + 2 ^ (n - 2) := by
              omega
        _ = 2 ^ n := by
          rw [← top_plus_two_next_dyadic_eq hn]
          omega
    · by_cases h2 : k2 = n - 1
      · have hk0' : k0 ≤ n - 2 := by omega
        have hk1' : k1 ≤ n - 2 := by omega
        have hp0 := hpow hk0'
        have hp1 := hpow hk1'
        rw [h2]
        calc
          2 ^ k0 + 2 ^ k1 + 2 ^ (n - 1)
              ≤ 2 ^ (n - 2) + 2 ^ (n - 2) + 2 ^ (n - 1) := by
                omega
          _ = 2 ^ n := by
            rw [← top_plus_two_next_dyadic_eq hn]
            omega
      · have hk0' : k0 ≤ n - 2 := by omega
        have hk1' : k1 ≤ n - 2 := by omega
        have hk2' : k2 ≤ n - 2 := by omega
        have hp0 := hpow hk0'
        have hp1 := hpow hk1'
        have hp2 := hpow hk2'
        have hbase :
            2 ^ k0 + 2 ^ k1 + 2 ^ k2
              ≤ 3 * 2 ^ (n - 2) := by
          omega
        have hthree :
            3 * 2 ^ (n - 2) ≤ 2 ^ n := by
          have heq := top_plus_two_next_dyadic_eq hn
          have hpowNext :
              2 ^ (n - 2) ≤ 2 ^ (n - 1) := by
            apply hpow
            omega
          omega
        exact hbase.trans hthree

/-- Three actual centres form a fixed-t terminal in the lower branch. -/
theorem three_centre_fixed_t_capacity
    {p : Fin 3 → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : Fin 3, CentreProjectiveCycle hp i) :
    (∑ i : Fin 3, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  have hdelta1 : delta < 1 := by linarith
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  let k0 := centreExponent (C 0) t
  let k1 := centreExponent (C 1) t
  let k2 := centreExponent (C 2) t
  have hk0 : k0 < n := by
    dsimp [k0]
    exact centreExponent_lt_n
      (C 0) n delta t (by omega) hdelta0 hdelta1 ht
  have hk1 : k1 < n := by
    dsimp [k1]
    exact centreExponent_lt_n
      (C 1) n delta t (by omega) hdelta0 hdelta1 ht
  have hk2 : k2 < n := by
    dsimp [k2]
    exact centreExponent_lt_n
      (C 2) n delta t (by omega) hdelta0 hdelta1 ht
  have h01 : ¬ (k0 = n - 1 ∧ k1 = n - 1) := by
    rintro ⟨h0, h1⟩
    have hs0 :=
      concrete_unit_deficit_is_sharp
        hp hcap hn hdelta0 hdelta1 ht hlam
        (0 : Fin 3) (C 0) (by simpa [k0] using h0)
    have hs1 :=
      concrete_unit_deficit_is_sharp
        hp hcap hn hdelta0 hdelta1 ht hlam
        (1 : Fin 3) (C 1) (by simpa [k1] using h1)
    exact two_sharp_no_third_small_delta
      hp hcap hdeltaHalf hlampos
      (i := (0 : Fin 3)) (j := (1 : Fin 3)) (k := (2 : Fin 3))
      (by decide) (by decide) (by decide) hs0 hs1
  have h02 : ¬ (k0 = n - 1 ∧ k2 = n - 1) := by
    rintro ⟨h0, h2⟩
    have hs0 :=
      concrete_unit_deficit_is_sharp
        hp hcap hn hdelta0 hdelta1 ht hlam
        (0 : Fin 3) (C 0) (by simpa [k0] using h0)
    have hs2 :=
      concrete_unit_deficit_is_sharp
        hp hcap hn hdelta0 hdelta1 ht hlam
        (2 : Fin 3) (C 2) (by simpa [k2] using h2)
    exact two_sharp_no_third_small_delta
      hp hcap hdeltaHalf hlampos
      (i := (0 : Fin 3)) (j := (2 : Fin 3)) (k := (1 : Fin 3))
      (by decide) (by decide) (by decide) hs0 hs2
  have h12 : ¬ (k1 = n - 1 ∧ k2 = n - 1) := by
    rintro ⟨h1, h2⟩
    have hs1 :=
      concrete_unit_deficit_is_sharp
        hp hcap hn hdelta0 hdelta1 ht hlam
        (1 : Fin 3) (C 1) (by simpa [k1] using h1)
    have hs2 :=
      concrete_unit_deficit_is_sharp
        hp hcap hn hdelta0 hdelta1 ht hlam
        (2 : Fin 3) (C 2) (by simpa [k2] using h2)
    exact two_sharp_no_third_small_delta
      hp hcap hdeltaHalf hlampos
      (i := (1 : Fin 3)) (j := (2 : Fin 3)) (k := (0 : Fin 3))
      (by decide) (by decide) (by decide) hs1 hs2
  have harith :=
    three_dyadic_terms_le_of_at_most_one_top
      hn hk0 hk1 hk2 h01 h02 h12
  simpa [k0, k1, k2, Fin.sum_univ_succ] using harith

#print axioms top_plus_two_next_dyadic_eq
#print axioms three_dyadic_terms_le_of_at_most_one_top
#print axioms three_centre_fixed_t_capacity

end JSP000404Research
