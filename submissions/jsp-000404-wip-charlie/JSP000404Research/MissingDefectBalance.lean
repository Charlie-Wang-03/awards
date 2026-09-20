import JSP000404Research.WeightedHansel
import Mathlib.Tactic

/-!
# Full-vertex versus multiple-missing defect balance

On `n+1` Boolean coordinates, a vertex specifying all coordinates contributes
weight one to weighted Hansel.  A vertex missing exactly one coordinate
contributes two.  A vertex missing two or more coordinates contributes more
than two and can therefore pay for fully specified vertices.

Let

  fullCount = #{v : specified v = univ}

and

  extra = sum_v (2^((n+1)-card(specified v)) - 2),

where natural subtraction makes the full and one-missing terms zero.
If

  fullCount <= extra + 1,

then weighted Hansel gives

  2*|V| - 1 <= 2^(n+1),

hence, by integrality, `|V| <= 2^n`.

This strictly weakens the previous "at most one full vertex" outlet and is
suited to a charging argument: every vertex missing at least two colours
supplies positive credit against full vertices.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Vertices whose partial Boolean word is fully specified. -/
noncomputable def fullSpecifiedVertices
    {V : Type*} [Fintype V] {k : ℕ}
    (specified : V → Finset (Fin k)) : Finset V := by
  classical
  exact Finset.univ.filter fun v => specified v = Finset.univ

/-- Extra Hansel weight beyond the baseline value two.  Full vertices and
one-missing vertices contribute zero; vertices missing at least two
coordinates contribute positive credit. -/
def extraMissingWeight
    {V : Type*} [Fintype V] {k : ℕ}
    (specified : V → Finset (Fin k)) : ℕ :=
  ∑ v : V, (2 ^ (k - (specified v).card) - 2)

theorem fullSpecifiedVertices_mem_iff
    {V : Type*} [Fintype V] {k : ℕ}
    (specified : V → Finset (Fin k)) (v : V) :
    v ∈ fullSpecifiedVertices specified ↔
      specified v = Finset.univ := by
  classical
  simp [fullSpecifiedVertices]

/-- Exact lower decomposition needed for the balance argument. -/
theorem two_mul_card_le_weighted_sum_add_full
    {V : Type*} [Fintype V] {k : ℕ}
    (specified : V → Finset (Fin k)) :
    2 * Fintype.card V ≤
      (∑ v : V, 2 ^ (k - (specified v).card)) +
        (fullSpecifiedVertices specified).card -
        extraMissingWeight specified := by
  classical
  -- We prove the equivalent termwise inequality before the final arithmetic
  -- rearrangement.  A full vertex has weight 1; every non-full vertex has
  -- weight at least 2, with all weight above 2 recorded by extraMissingWeight.
  have hpoint :
      ∀ v : V,
        2 + (2 ^ (k - (specified v).card) - 2) ≤
          2 ^ (k - (specified v).card) +
            (if specified v = Finset.univ then 1 else 0) := by
    intro v
    by_cases hfull : specified v = Finset.univ
    · rw [hfull]
      simp
    · have hcard_le : (specified v).card ≤ k := by
        simpa using Finset.card_le_univ (specified v)
      have hcard_ne : (specified v).card ≠ k := by
        intro h
        apply hfull
        exact Finset.eq_univ_of_card _ (by simpa using h)
      have hcard_lt : (specified v).card < k := by omega
      have hexp : 1 ≤ k - (specified v).card := by omega
      have htwo : 2 ≤ 2 ^ (k - (specified v).card) := by
        simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
      simp [hfull]
      omega
  have hsum :
      (∑ v : V,
          (2 + (2 ^ (k - (specified v).card) - 2))) ≤
        ∑ v : V,
          (2 ^ (k - (specified v).card) +
            (if specified v = Finset.univ then 1 else 0)) :=
    Finset.sum_le_sum fun v _ => hpoint v
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hfullsum :
      (∑ v : V, if specified v = Finset.univ then 1 else 0) =
        (fullSpecifiedVertices specified).card := by
    classical
    simp [fullSpecifiedVertices]
  rw [hfullsum] at hsum
  have hconst : (∑ _v : V, 2) = 2 * Fintype.card V := by
    simp [Nat.mul_comm]
  rw [hconst] at hsum
  dsimp [extraMissingWeight]
  omega

/-- Main defect-balance capacity theorem on n+1 coordinates. -/
theorem hansel_card_le_two_pow_of_full_extra_balance
    {V : Type*} [Fintype V] {n : ℕ}
    (bit : V → Fin (n + 1) → Bool)
    (specified : V → Finset (Fin (n + 1)))
    (hsep : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i)
    (hbalance :
      (fullSpecifiedVertices specified).card ≤
        extraMissingWeight specified + 1) :
    Fintype.card V ≤ 2 ^ n := by
  classical
  have hweighted :
      (∑ v : V, 2 ^ ((n + 1) - (specified v).card)) ≤
        2 ^ (n + 1) :=
    weighted_hansel bit specified hsep
  have hlower :=
    two_mul_card_le_weighted_sum_add_full specified
  have htwo :
      2 * Fintype.card V ≤ 2 ^ (n + 1) + 1 := by
    omega
  rw [pow_succ] at htwo
  omega

/-- The old at-most-one-full criterion is an immediate special case. -/
theorem hansel_card_le_two_pow_of_atMostOne_full_via_balance
    {V : Type*} [Fintype V] {n : ℕ}
    (bit : V → Fin (n + 1) → Bool)
    (specified : V → Finset (Fin (n + 1)))
    (hsep : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i)
    (hfull :
      (fullSpecifiedVertices specified).card ≤ 1) :
    Fintype.card V ≤ 2 ^ n := by
  apply hansel_card_le_two_pow_of_full_extra_balance bit specified hsep
  have hz : 0 ≤ extraMissingWeight specified := Nat.zero_le _
  omega

/-- Direction-band specialization. -/
theorem unitBand_card_le_two_pow_of_full_extra_balance
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width) (n : ℕ)
    (hwidth : width ≤ (n + 1 : ℕ))
    (hbalance :
      (fullSpecifiedVertices
        (DirectionData.incidentBands D (n + 1))).card ≤
      extraMissingWeight
        (DirectionData.incidentBands D (n + 1)) + 1) :
    Fintype.card V ≤ 2 ^ n := by
  exact hansel_card_le_two_pow_of_full_extra_balance
    (DirectionData.bandBit D (n + 1))
    (DirectionData.incidentBands D (n + 1))
    (DirectionData.unitBand_separates D (n + 1) (by
      exact_mod_cast hwidth))
    hbalance

#print axioms fullSpecifiedVertices_mem_iff
#print axioms two_mul_card_le_weighted_sum_add_full
#print axioms hansel_card_le_two_pow_of_full_extra_balance
#print axioms unitBand_card_le_two_pow_of_full_extra_balance

end JSP000404Research
