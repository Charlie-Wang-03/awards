
import JSP000404Research.MinimalOverweightKraftProfile
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# Parity rigidity of the minimum exponent layer

In the one-child minimal-overweight situation, let

  a = exponent(r) = min_i exponent(i).

MinimalOverweightKraftProfile proves

  sum_i 2^(exponent(i)-a) = 2^(n-a) + 1.

If a<n, the right-hand side is odd.

On the left, a term 2^(exponent(i)-a) is odd exactly when exponent(i)=a:
the minimum-layer vertices contribute 1, while every higher layer contributes
an even power of two.

Therefore the number of minimum-exponent vertices is odd.

This gives a genuinely new discrete restriction on any minimal overweight
profile compatible with one bounded minimum deletion child.
-/

namespace JSP000404Research

open scoped BigOperators

noncomputable def minimumExponentVertices
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (r : V) : Finset V := by
  classical
  exact Finset.univ.filter fun i =>
    exponent i = exponent r

@[simp] theorem mem_minimumExponentVertices
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (r i : V) :
    i ∈ minimumExponentVertices exponent r ↔
      exponent i = exponent r := by
  classical
  simp [minimumExponentVertices]

/-- Under minimum-exponent normalization, the odd dyadic terms are exactly
the minimum layer. -/
theorem odd_two_pow_normalizedExponent_iff_minimum
    {V : Type*}
    (exponent : V → ℕ)
    (r i : V)
    (hmin : ∀ j : V, exponent r ≤ exponent j) :
    Odd (2 ^ normalizedExponent exponent r i)
      ↔
    exponent i = exponent r := by
  by_cases hi : exponent i = exponent r
  · simp [normalizedExponent, hi]
  · have hlt :
        exponent r < exponent i := by
      exact lt_of_le_of_ne (hmin i) (Ne.symm hi)
    have hpos :
        0 < normalizedExponent exponent r i := by
      unfold normalizedExponent
      exact Nat.sub_pos_of_lt hlt
    have hne :
        normalizedExponent exponent r i ≠ 0 :=
      Nat.ne_of_gt hpos
    rw [odd_pow_iff hne]
    norm_num

/-- The normalized full overweight mass is odd whenever the minimum exponent
lies strictly below n. -/
theorem normalizedTotalDyadicWeight_odd_of_child_bound
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (r : V)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hminStrict : exponent r < n)
    (hmonoR :
      ∀ i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchildR :
      deletionPostWeight after r ≤ 2 ^ n)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    Odd (normalizedTotalDyadicWeight exponent r) := by
  have hEq :=
    normalized_total_eq_kraft_plus_one_of_child_bound
      exponent after n r hexp hmonoR hover hchildR hmin
  have hNpos :
      0 < n - exponent r :=
    Nat.sub_pos_of_lt hminStrict
  have hEven :
      Even (2 ^ (n - exponent r)) :=
    even_two.pow_of_ne_zero (Nat.ne_of_gt hNpos)
  rw [hEq]
  exact hEven.add_one

/-- Main parity theorem: the minimum exponent occurs an odd number of times. -/
theorem minimumExponentVertices_card_odd_of_child_bound
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (r : V)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hminStrict : exponent r < n)
    (hmonoR :
      ∀ i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchildR :
      deletionPostWeight after r ≤ 2 ^ n)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    Odd (minimumExponentVertices exponent r).card := by
  classical
  have hOddTotal :=
    normalizedTotalDyadicWeight_odd_of_child_bound
      exponent after n r hexp hminStrict
      hmonoR hover hchildR hmin
  have hOddSum :
      Odd (∑ i ∈ (Finset.univ : Finset V),
        2 ^ normalizedExponent exponent r i) := by
    simpa [normalizedTotalDyadicWeight] using hOddTotal
  have hOddCard :
      Odd
        ((Finset.univ.filter fun i : V =>
          Odd (2 ^ normalizedExponent exponent r i)).card) :=
    (Finset.odd_sum_iff_odd_card_odd
      (s := (Finset.univ : Finset V))
      (fun i => 2 ^ normalizedExponent exponent r i)).1
      hOddSum
  have hset :
      (Finset.univ.filter fun i : V =>
        Odd (2 ^ normalizedExponent exponent r i))
        =
      minimumExponentVertices exponent r := by
    ext i
    simp [minimumExponentVertices,
      odd_two_pow_normalizedExponent_iff_minimum
        exponent r i hmin]
  rw [hset] at hOddCard
  exact hOddCard

/-- In particular the minimum layer cannot have cardinality two. -/
theorem minimumExponentVertices_card_ne_two_of_child_bound
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (r : V)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hminStrict : exponent r < n)
    (hmonoR :
      ∀ i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchildR :
      deletionPostWeight after r ≤ 2 ^ n)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    (minimumExponentVertices exponent r).card ≠ 2 := by
  have hOdd :=
    minimumExponentVertices_card_odd_of_child_bound
      exponent after n r hexp hminStrict
      hmonoR hover hchildR hmin
  intro htwo
  rw [htwo] at hOdd
  norm_num at hOdd


/-- An odd finite subset is either of size one, of size three, or it contains
a point outside any prescribed triple. -/
theorem odd_finset_one_or_three_or_exists_outside_triple
    {V : Type*} [DecidableEq V]
    (S : Finset V)
    (hodd : Odd S.card)
    (a b c : V) :
    S.card = 1 ∨ S.card = 3 ∨
      ∃ r : V, r ∈ S ∧ r ≠ a ∧ r ≠ b ∧ r ≠ c := by
  by_cases hout :
      ∃ r : V, r ∈ S ∧ r ≠ a ∧ r ≠ b ∧ r ≠ c
  · exact Or.inr (Or.inr hout)
  · have hsub : S ⊆ {a, b, c} := by
      intro x hx
      have hcases : x = a ∨ x = b ∨ x = c := by
        by_contra hnot
        push_neg at hnot
        exact hout ⟨x, hx, hnot.1, hnot.2.1, hnot.2.2⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hcases
    have hcardLe : S.card ≤ 3 := by
      have h :=
        Finset.card_le_card hsub
      have htriple :
          ({a, b, c} : Finset V).card ≤ 3 := by
        simp
        omega
      exact h.trans htriple
    have hmod : S.card % 2 = 1 :=
      Nat.odd_iff.mp hodd
    omega

/-- Minimum-layer trichotomy relative to any prescribed triple. -/
theorem minimum_layer_one_or_three_or_avoids_triple_of_child_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (r₀ : V)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hminStrict : exponent r₀ < n)
    (hmonoR :
      ∀ i, i ≠ r₀ → exponent i ≤ after r₀ i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchildR :
      deletionPostWeight after r₀ ≤ 2 ^ n)
    (hmin : ∀ i : V, exponent r₀ ≤ exponent i)
    (a b c : V) :
    (minimumExponentVertices exponent r₀).card = 1
      ∨
    (minimumExponentVertices exponent r₀).card = 3
      ∨
    ∃ r : V,
      r ∈ minimumExponentVertices exponent r₀ ∧
      r ≠ a ∧ r ≠ b ∧ r ≠ c := by
  have hodd :=
    minimumExponentVertices_card_odd_of_child_bound
      exponent after n r₀ hexp hminStrict
      hmonoR hover hchildR hmin
  exact odd_finset_one_or_three_or_exists_outside_triple
    (minimumExponentVertices exponent r₀)
    hodd a b c

#print axioms odd_two_pow_normalizedExponent_iff_minimum
#print axioms normalizedTotalDyadicWeight_odd_of_child_bound
#print axioms minimumExponentVertices_card_odd_of_child_bound
#print axioms minimumExponentVertices_card_ne_two_of_child_bound

end JSP000404Research
