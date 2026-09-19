import JSP000404Research.WeightedHansel
import Mathlib.Tactic

/-!
# Weighted Hansel defect consequences

Closed combinatorial consequences of `weighted_hansel`.

The main theorem is the exact defect form appearing in the Erdős--Szekeres
even-partition argument: if a vertex leaves `ν(v)` Boolean coordinates free,
then the total excess weight `∑ (2^ν(v) - 1)` is bounded by the global
deficiency `2^k - |V|`.

No geometry is used here.  The remaining JSP-000404 work is to construct the
relevant partial Boolean code from the sharp ordered-direction data.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Exact defect form of the weighted Hansel inequality.

If `specified v` is the set of Boolean coordinates fixed at `v`, then
`k - (specified v).card` is the number of free coordinates at `v`.
The excess free-subcube capacity is bounded by the missing ambient vertices.
-/
theorem weighted_hansel_defect
    {V : Type*} [Fintype V] {k : ℕ}
    (bit : V → Fin k → Bool) (specified : V → Finset (Fin k))
    (hsep : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i) :
    ∑ v, (2 ^ (k - (specified v).card) - 1) ≤
      2 ^ k - Fintype.card V := by
  classical
  have hweighted :
      ∑ v, 2 ^ (k - (specified v).card) ≤ 2 ^ k :=
    weighted_hansel bit specified hsep
  have hsplit :
      (∑ v, (2 ^ (k - (specified v).card) - 1)) + Fintype.card V =
        ∑ v, 2 ^ (k - (specified v).card) := by
    rw [← Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    apply Finset.sum_congr rfl
    intro v _
    have hpos : 0 < 2 ^ (k - (specified v).card) := by positivity
    omega
  have hadd :
      (∑ v, (2 ^ (k - (specified v).card) - 1)) + Fintype.card V ≤ 2 ^ k := by
    rw [hsplit]
    exact hweighted
  omega

/-- If one vertex leaves at least one Boolean coordinate free, the ordinary
Hansel capacity improves from `|V| ≤ 2^k` to `|V| + 1 ≤ 2^k`. -/
theorem weighted_hansel_one_missing
    {V : Type*} [Fintype V] {k : ℕ}
    (bit : V → Fin k → Bool) (specified : V → Finset (Fin k))
    (hsep : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i)
    (v : V) (hmissing : specified v ≠ Finset.univ) :
    Fintype.card V + 1 ≤ 2 ^ k := by
  classical
  have hdefect := weighted_hansel_defect bit specified hsep
  have hcard_le : (specified v).card ≤ k := by
    simpa using Finset.card_le_univ (specified v)
  have hcard_ne : (specified v).card ≠ k := by
    intro heq
    apply hmissing
    exact Finset.eq_univ_of_card (specified v) (by simpa using heq)
  have hcard_lt : (specified v).card < k := lt_of_le_of_ne hcard_le hcard_ne
  have hexp : 1 ≤ k - (specified v).card := by omega
  have hpow : 2 ≤ 2 ^ (k - (specified v).card) := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
  have hterm : 1 ≤ 2 ^ (k - (specified v).card) - 1 := by omega
  have hsum :
      1 ≤ ∑ x, (2 ^ (k - (specified x).card) - 1) := by
    calc
      1 ≤ 2 ^ (k - (specified v).card) - 1 := hterm
      _ ≤ ∑ x, (2 ^ (k - (specified x).card) - 1) := by
        exact Finset.single_le_sum
          (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ v)
  omega

/-- If every vertex leaves at least one Boolean coordinate free, the vertex
capacity is halved: `2 * |V| ≤ 2^k`. -/
theorem weighted_hansel_all_missing
    {V : Type*} [Fintype V] {k : ℕ}
    (bit : V → Fin k → Bool) (specified : V → Finset (Fin k))
    (hsep : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i)
    (hmissing : ∀ v, specified v ≠ Finset.univ) :
    2 * Fintype.card V ≤ 2 ^ k := by
  classical
  have hdefect := weighted_hansel_defect bit specified hsep
  have hpoint : ∀ v : V, 1 ≤ 2 ^ (k - (specified v).card) - 1 := by
    intro v
    have hcard_le : (specified v).card ≤ k := by
      simpa using Finset.card_le_univ (specified v)
    have hcard_ne : (specified v).card ≠ k := by
      intro heq
      apply hmissing v
      exact Finset.eq_univ_of_card (specified v) (by simpa using heq)
    have hcard_lt : (specified v).card < k := lt_of_le_of_ne hcard_le hcard_ne
    have hexp : 1 ≤ k - (specified v).card := by omega
    have hpow : 2 ≤ 2 ^ (k - (specified v).card) := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
    omega
  have hsum :
      Fintype.card V ≤ ∑ v, (2 ^ (k - (specified v).card) - 1) := by
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset V))
        (fun v _ => hpoint v))
  omega

#print axioms weighted_hansel_defect
#print axioms weighted_hansel_one_missing
#print axioms weighted_hansel_all_missing

end JSP000404Research
