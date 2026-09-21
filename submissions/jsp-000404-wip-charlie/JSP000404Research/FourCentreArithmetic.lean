import JSP000404Research.ThreeCentreTerminal
import Mathlib.Tactic

/-!
# Four-term dyadic arithmetic reduction

For four exponents k0..k3 with k_i<n, the sharp dyadic capacity follows from
two structural facts:

1. at most one exponent is n-1;
2. if some exponent is n-1, then among the remaining three at most one is
   n-2.

Indeed, with no top exponent all four terms are at most 2^(n-2).  If one top
exponent is present, the remaining three terms satisfy the already-proved
three-term estimate at level n-1.

Thus the four-centre geometric terminal reduces to exactly one statement:
outside a sharp centre, there cannot be two deficit-two centres.
-/

namespace JSP000404Research

theorem four_next_dyadic_eq
    {n : ℕ} (hn : 2 ≤ n) :
    4 * 2 ^ (n - 2) = 2 ^ n := by
  let m := n - 2
  have hnm : n = m + 2 := by
    dsimp [m]
    omega
  rw [hnm]
  simp [pow_succ]
  ring

theorem four_dyadic_terms_le_of_sharp_structure
    {n : ℕ}
    (hn : 3 ≤ n)
    (k : Fin 4 → ℕ)
    (hk : ∀ i, k i < n)
    (htop :
      ∀ {a b : Fin 4}, a ≠ b →
        ¬ (k a = n - 1 ∧ k b = n - 1))
    (hnext :
      ∀ {s a b : Fin 4},
        s ≠ a → s ≠ b → a ≠ b →
        k s = n - 1 →
        ¬ (k a = n - 2 ∧ k b = n - 2)) :
    2 ^ k 0 + 2 ^ k 1 + 2 ^ k 2 + 2 ^ k 3 ≤ 2 ^ n := by
  have hpow :
      ∀ {a b : ℕ}, a ≤ b → 2 ^ a ≤ 2 ^ b := by
    intro a b hab
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hab
  by_cases h0 : k 0 = n - 1
  · have h1lt : k 1 < n - 1 := by
      have hne : k 1 ≠ n - 1 := by
        intro h1
        exact htop (a := (0 : Fin 4)) (b := (1 : Fin 4))
          (by decide) ⟨h0, h1⟩
      omega
    have h2lt : k 2 < n - 1 := by
      have hne : k 2 ≠ n - 1 := by
        intro h2
        exact htop (a := (0 : Fin 4)) (b := (2 : Fin 4))
          (by decide) ⟨h0, h2⟩
      omega
    have h3lt : k 3 < n - 1 := by
      have hne : k 3 ≠ n - 1 := by
        intro h3
        exact htop (a := (0 : Fin 4)) (b := (3 : Fin 4))
          (by decide) ⟨h0, h3⟩
      omega
    have h12 :
        ¬ (k 1 = (n - 1) - 1 ∧ k 2 = (n - 1) - 1) := by
      have h :=
        hnext (s := (0 : Fin 4)) (a := (1 : Fin 4)) (b := (2 : Fin 4))
          (by decide) (by decide) (by decide) h0
      simpa [Nat.sub_sub] using h
    have h13 :
        ¬ (k 1 = (n - 1) - 1 ∧ k 3 = (n - 1) - 1) := by
      have h :=
        hnext (s := (0 : Fin 4)) (a := (1 : Fin 4)) (b := (3 : Fin 4))
          (by decide) (by decide) (by decide) h0
      simpa [Nat.sub_sub] using h
    have h23 :
        ¬ (k 2 = (n - 1) - 1 ∧ k 3 = (n - 1) - 1) := by
      have h :=
        hnext (s := (0 : Fin 4)) (a := (2 : Fin 4)) (b := (3 : Fin 4))
          (by decide) (by decide) (by decide) h0
      simpa [Nat.sub_sub] using h
    have htail :=
      three_dyadic_terms_le_of_at_most_one_top
        (n := n - 1)
        (k0 := k 1) (k1 := k 2) (k2 := k 3)
        (by omega) h1lt h2lt h3lt h12 h13 h23
    rw [h0]
    have hdouble :
        2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
      have hn1 : n - 1 + 1 = n := by omega
      rw [← pow_succ, hn1]
      ring
    linarith
  · by_cases h1 : k 1 = n - 1
    · have h0lt : k 0 < n - 1 := by omega
      have h2lt : k 2 < n - 1 := by
        have hne : k 2 ≠ n - 1 := by
          intro h2
          exact htop (a := (1 : Fin 4)) (b := (2 : Fin 4))
            (by decide) ⟨h1, h2⟩
        omega
      have h3lt : k 3 < n - 1 := by
        have hne : k 3 ≠ n - 1 := by
          intro h3
          exact htop (a := (1 : Fin 4)) (b := (3 : Fin 4))
            (by decide) ⟨h1, h3⟩
        omega
      have h02 :
          ¬ (k 0 = (n - 1) - 1 ∧ k 2 = (n - 1) - 1) := by
        have h :=
          hnext (s := (1 : Fin 4)) (a := (0 : Fin 4)) (b := (2 : Fin 4))
            (by decide) (by decide) (by decide) h1
        simpa [Nat.sub_sub] using h
      have h03 :
          ¬ (k 0 = (n - 1) - 1 ∧ k 3 = (n - 1) - 1) := by
        have h :=
          hnext (s := (1 : Fin 4)) (a := (0 : Fin 4)) (b := (3 : Fin 4))
            (by decide) (by decide) (by decide) h1
        simpa [Nat.sub_sub] using h
      have h23 :
          ¬ (k 2 = (n - 1) - 1 ∧ k 3 = (n - 1) - 1) := by
        have h :=
          hnext (s := (1 : Fin 4)) (a := (2 : Fin 4)) (b := (3 : Fin 4))
            (by decide) (by decide) (by decide) h1
        simpa [Nat.sub_sub] using h
      have htail :=
        three_dyadic_terms_le_of_at_most_one_top
          (n := n - 1)
          (k0 := k 0) (k1 := k 2) (k2 := k 3)
          (by omega) h0lt h2lt h3lt h02 h03 h23
      rw [h1]
      have hdouble :
          2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
        have hn1 : n - 1 + 1 = n := by omega
        rw [← pow_succ, hn1]
        ring
      linarith
    · by_cases h2 : k 2 = n - 1
      · have h0lt : k 0 < n - 1 := by omega
        have h1lt : k 1 < n - 1 := by omega
        have h3lt : k 3 < n - 1 := by
          have hne : k 3 ≠ n - 1 := by
            intro h3
            exact htop (a := (2 : Fin 4)) (b := (3 : Fin 4))
              (by decide) ⟨h2, h3⟩
          omega
        have h01 :
            ¬ (k 0 = (n - 1) - 1 ∧ k 1 = (n - 1) - 1) := by
          have h :=
            hnext (s := (2 : Fin 4)) (a := (0 : Fin 4)) (b := (1 : Fin 4))
              (by decide) (by decide) (by decide) h2
          simpa [Nat.sub_sub] using h
        have h03 :
            ¬ (k 0 = (n - 1) - 1 ∧ k 3 = (n - 1) - 1) := by
          have h :=
            hnext (s := (2 : Fin 4)) (a := (0 : Fin 4)) (b := (3 : Fin 4))
              (by decide) (by decide) (by decide) h2
          simpa [Nat.sub_sub] using h
        have h13 :
            ¬ (k 1 = (n - 1) - 1 ∧ k 3 = (n - 1) - 1) := by
          have h :=
            hnext (s := (2 : Fin 4)) (a := (1 : Fin 4)) (b := (3 : Fin 4))
              (by decide) (by decide) (by decide) h2
          simpa [Nat.sub_sub] using h
        have htail :=
          three_dyadic_terms_le_of_at_most_one_top
            (n := n - 1)
            (k0 := k 0) (k1 := k 1) (k2 := k 3)
            (by omega) h0lt h1lt h3lt h01 h03 h13
        rw [h2]
        have hdouble :
            2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
          have hn1 : n - 1 + 1 = n := by omega
          rw [← pow_succ, hn1]
          ring
        linarith
      · by_cases h3 : k 3 = n - 1
        · have h0lt : k 0 < n - 1 := by omega
          have h1lt : k 1 < n - 1 := by omega
          have h2lt : k 2 < n - 1 := by omega
          have h01 :
              ¬ (k 0 = (n - 1) - 1 ∧ k 1 = (n - 1) - 1) := by
            have h :=
              hnext (s := (3 : Fin 4)) (a := (0 : Fin 4)) (b := (1 : Fin 4))
                (by decide) (by decide) (by decide) h3
            simpa [Nat.sub_sub] using h
          have h02 :
              ¬ (k 0 = (n - 1) - 1 ∧ k 2 = (n - 1) - 1) := by
            have h :=
              hnext (s := (3 : Fin 4)) (a := (0 : Fin 4)) (b := (2 : Fin 4))
                (by decide) (by decide) (by decide) h3
            simpa [Nat.sub_sub] using h
          have h12 :
              ¬ (k 1 = (n - 1) - 1 ∧ k 2 = (n - 1) - 1) := by
            have h :=
              hnext (s := (3 : Fin 4)) (a := (1 : Fin 4)) (b := (2 : Fin 4))
                (by decide) (by decide) (by decide) h3
            simpa [Nat.sub_sub] using h
          have htail :=
            three_dyadic_terms_le_of_at_most_one_top
              (n := n - 1)
              (k0 := k 0) (k1 := k 1) (k2 := k 2)
              (by omega) h0lt h1lt h2lt h01 h02 h12
          rw [h3]
          have hdouble :
              2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
            have hn1 : n - 1 + 1 = n := by omega
            rw [← pow_succ, hn1]
            ring
          linarith
        · have hk0' : k 0 ≤ n - 2 := by omega
          have hk1' : k 1 ≤ n - 2 := by omega
          have hk2' : k 2 ≤ n - 2 := by omega
          have hk3' : k 3 ≤ n - 2 := by omega
          have hp0 := hpow hk0'
          have hp1 := hpow hk1'
          have hp2 := hpow hk2'
          have hp3 := hpow hk3'
          have hsum :
              2 ^ k 0 + 2 ^ k 1 + 2 ^ k 2 + 2 ^ k 3
                ≤ 4 * 2 ^ (n - 2) := by
            omega
          rw [four_next_dyadic_eq (by omega : 2 ≤ n)] at hsum
          exact hsum

#print axioms four_next_dyadic_eq
#print axioms four_dyadic_terms_le_of_sharp_structure

end JSP000404Research
