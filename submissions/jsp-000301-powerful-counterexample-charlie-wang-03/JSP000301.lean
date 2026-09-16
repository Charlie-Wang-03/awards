import Mathlib

namespace JSP000301

/-- A natural number is powerful when every prime divisor occurs to exponent at least two. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- A natural number is a perfect square. -/
def IsSquare (n : ℕ) : Prop :=
  ∃ k : ℕ, k ^ 2 = n

/-- Every number of the form a^2 b^3 is powerful. -/
lemma powerful_sq_mul_cube (a b : ℕ) : Powerful (a ^ 2 * b ^ 3) := by
  intro p hp hdiv
  rcases hp.dvd_mul.mp hdiv with ha | hb
  · have hpa : p ∣ a := hp.dvd_of_dvd_pow ha
    rcases hpa with ⟨c, rfl⟩
    refine ⟨c ^ 2 * b ^ 3, ?_⟩
    ring
  · have hpb : p ∣ b := hp.dvd_of_dvd_pow hb
    rcases hpb with ⟨c, rfl⟩
    refine ⟨a ^ 2 * p * c ^ 3, ?_⟩
    ring

theorem powerful_12167 : Powerful 12167 := by
  exact powerful_sq_mul_cube 1 23

theorem powerful_12168 : Powerful 12168 := by
  exact powerful_sq_mul_cube 39 2

private lemma not_square_in_gap {n : ℕ} (hlo : 110 ^ 2 < n) (hhi : n < 111 ^ 2) :
    ¬ IsSquare n := by
  rintro ⟨k, hk⟩
  have hcases : k ≤ 110 ∨ 111 ≤ k := by omega
  rcases hcases with hle | hge
  · have hmul : k * k ≤ 110 * 110 := Nat.mul_le_mul hle hle
    rw [pow_two] at hk
    norm_num at hlo hmul
    omega
  · have hmul : 111 * 111 ≤ k * k := Nat.mul_le_mul hge hge
    rw [pow_two] at hk
    norm_num at hhi hmul
    omega

theorem not_square_12167 : ¬ IsSquare 12167 :=
  not_square_in_gap (by norm_num) (by norm_num)

theorem not_square_12168 : ¬ IsSquare 12168 :=
  not_square_in_gap (by norm_num) (by norm_num)

/-- The explicit consecutive counterexample recorded for JSP-000301. -/
theorem jsp_000301_counterexample :
    ∃ n : ℕ, 0 < n ∧ Powerful n ∧ Powerful (n + 1) ∧
      ¬ IsSquare n ∧ ¬ IsSquare (n + 1) := by
  refine ⟨12167, by norm_num, powerful_12167, ?_, not_square_12167, ?_⟩
  · simpa using powerful_12168
  · simpa using not_square_12168

/-- Negative answer to the scoped JSP-000301 yes/no question. -/
theorem jsp_000301 :
    ¬ ∀ n : ℕ, 0 < n → Powerful n → Powerful (n + 1) →
      IsSquare n ∨ IsSquare (n + 1) := by
  intro h
  have hs := h 12167 (by norm_num) powerful_12167 (by simpa using powerful_12168)
  rcases hs with hs | hs
  · exact not_square_12167 hs
  · exact not_square_12168 (by simpa using hs)

end JSP000301
