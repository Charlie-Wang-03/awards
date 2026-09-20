import JSP000404Research.WeightedHansel
import Mathlib.Tactic

/-!
# One missing coordinate saves one full Boolean bit

Weighted Hansel already gives

  sum_v 2^((n+1) - card(specified v)) <= 2^(n+1).

If every vertex misses at least one of the n+1 coordinates, then every summand
on the left is at least two.  Therefore

  2 * |V| <= 2^(n+1),

and hence

  |V| <= 2^n.

This is a useful codimension-one outlet for JSP-000404: a geometric phase for
which every vertex misses at least one standard direction band would already
close the lower branch, without any residual recolouring.
-/

namespace JSP000404Research

open scoped BigOperators

/-- A family of pairwise separated partial Boolean words on n+1 coordinates
has at most 2^n vertices if every word leaves at least one coordinate
unspecified. -/
theorem hansel_card_le_two_pow_of_every_vertex_missing
    {V : Type*} [Fintype V] {n : ℕ}
    (bit : V → Fin (n + 1) → Bool)
    (specified : V → Finset (Fin (n + 1)))
    (hsep : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i)
    (hmissing : ∀ v, specified v ≠ Finset.univ) :
    Fintype.card V ≤ 2 ^ n := by
  classical
  have hterm :
      ∀ v : V, 2 ≤ 2 ^ ((n + 1) - (specified v).card) := by
    intro v
    have hcard_le : (specified v).card ≤ n + 1 := by
      have h :=
        Finset.card_le_card (Finset.subset_univ (specified v))
      simpa using h
    have hcard_lt : (specified v).card < n + 1 := by
      by_contra hnot
      have heq : (specified v).card = n + 1 := by omega
      apply hmissing v
      apply Finset.eq_univ_of_card
      simpa using heq
    have hexp : 1 ≤ (n + 1) - (specified v).card := by
      omega
    calc
      2 = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ ((n + 1) - (specified v).card) :=
        Nat.pow_le_pow_right (by decide) hexp
  have hlower :
      Fintype.card V * 2 ≤
        ∑ v : V, 2 ^ ((n + 1) - (specified v).card) := by
    have hs :
        (∑ _v : V, 2) ≤
          ∑ v : V, 2 ^ ((n + 1) - (specified v).card) :=
      Finset.sum_le_sum fun v _ => hterm v
    simpa [Nat.mul_comm] using hs
  have hupper :=
    weighted_hansel bit specified hsep
  have htwo :
      Fintype.card V * 2 ≤ 2 ^ (n + 1) :=
    hlower.trans hupper
  rw [pow_succ] at htwo
  omega

/-- Direction-band specialization: n+1 standard unit-band coordinates already
have sharp 2^n cardinality capacity as soon as every vertex misses one band. -/
theorem unitBand_card_le_two_pow_of_every_vertex_missing
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width) (n : ℕ)
    (hwidth : width ≤ n + 1)
    (hmissing :
      ∀ v, DirectionData.incidentBands D (n + 1) v ≠ Finset.univ) :
    Fintype.card V ≤ 2 ^ n := by
  apply hansel_card_le_two_pow_of_every_vertex_missing
    (DirectionData.bandBit D (n + 1))
    (DirectionData.incidentBands D (n + 1))
  · exact DirectionData.unitBand_separates D (n + 1) (by
      exact_mod_cast hwidth)
  · exact hmissing

#print axioms hansel_card_le_two_pow_of_every_vertex_missing
#print axioms unitBand_card_le_two_pow_of_every_vertex_missing

end JSP000404Research
