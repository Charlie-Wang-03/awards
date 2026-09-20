import JSP000404Research.BinaryEdgePartition
import Mathlib.Tactic

/-!
# Missing-vertex defect for a binary edge partition

Erdos--Szekeres Lemma 4 is stronger than the ordinary `2^k` capacity
bound.  Every vertex which misses at least one colour contributes at least one
unit of Boolean-cube defect.

Thus, for any chosen finite set `Q` of vertices, if every vertex of `Q`
misses some active colour, then

  |V| + |Q| <= 2^k.

This is the exact combinatorial outlet used by the adaptive even-partition
route: geometry may focus on manufacturing a single missing colour at many
selected vertices, rather than reducing the active-colour count everywhere.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Arbitrarily many prescribed missing vertices contribute additively to the
weighted Hansel defect. -/
theorem weighted_hansel_missing_finset
    {V : Type*} [Fintype V] {k : ℕ}
    (bit : V → Fin k → Bool)
    (specified : V → Finset (Fin k))
    (hsep : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i)
    (Q : Finset V)
    (hmissing : ∀ v ∈ Q, specified v ≠ Finset.univ) :
    Fintype.card V + Q.card ≤ 2 ^ k := by
  classical
  let defectTerm : V → ℕ :=
    fun v => 2 ^ (k - (specified v).card) - 1
  have hpoint :
      ∀ v : V, (if v ∈ Q then 1 else 0) ≤ defectTerm v := by
    intro v
    by_cases hvQ : v ∈ Q
    · simp only [if_pos hvQ]
      have hcard_le : (specified v).card ≤ k := by
        simpa using Finset.card_le_univ (specified v)
      have hcard_ne : (specified v).card ≠ k := by
        intro heq
        apply hmissing v hvQ
        exact Finset.eq_univ_of_card
          (specified v) (by simpa using heq)
      have hcard_lt : (specified v).card < k := by
        omega
      have hexp : 1 ≤ k - (specified v).card := by
        omega
      have hpow : 2 ≤ 2 ^ (k - (specified v).card) := by
        simpa using
          Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
      dsimp [defectTerm]
      omega
    · simp [hvQ, defectTerm]
  have hQ :
      Q.card ≤ ∑ v : V, defectTerm v := by
    have hs :
        (∑ v : V, if v ∈ Q then 1 else 0) ≤
          ∑ v : V, defectTerm v :=
      Finset.sum_le_sum fun v _ => hpoint v
    simpa using hs
  have hdefect :
      (∑ v : V, defectTerm v) ≤
        2 ^ k - Fintype.card V := by
    dsimp [defectTerm]
    exact weighted_hansel_defect bit specified hsep
  omega

namespace BinaryEdgePartition

/-- Binary-edge-partition specialization of the finite missing-vertex defect. -/
theorem card_add_missing_finset_le
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : BinaryEdgePartition V k)
    (Q : Finset V)
    (hmissing : ∀ v ∈ Q, active C v ≠ Finset.univ) :
    Fintype.card V + Q.card ≤ 2 ^ k := by
  exact weighted_hansel_missing_finset
    C.bit (active C) (separates C) Q hmissing

/-- A common designated colour absent at every selected vertex is enough. -/
theorem card_add_finset_le_of_common_missing_colour
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (C : BinaryEdgePartition V k)
    (Q : Finset V) (c : Fin k)
    (hmissing : ∀ v ∈ Q, c ∉ active C v) :
    Fintype.card V + Q.card ≤ 2 ^ k := by
  apply card_add_missing_finset_le C Q
  intro v hvQ hfull
  have hc : c ∈ active C v := by
    rw [hfull]
    simp
  exact hmissing v hvQ hc

#print axioms card_add_missing_finset_le
#print axioms card_add_finset_le_of_common_missing_colour

end BinaryEdgePartition

#print axioms weighted_hansel_missing_finset

end JSP000404Research
