import Mathlib.Tactic

/-!
# Four labels in an interval of span three

A four-element finite set of natural numbers contained in
  {m,m+1,m+2,m+3}
must contain both interior labels m+1 and m+2.

This tiny arithmetic lemma is useful in the remaining JSP-000404
two-bad-minimum palette rigidity.
-/

namespace JSP000404Research

theorem finset_card_four_interval_three_inner_mem
    (S : Finset ℕ) (m : ℕ)
    (hcard : S.card = 4)
    (hbounds :
      ∀ q ∈ S, m ≤ q ∧ q ≤ m + 3) :
    m + 1 ∈ S ∧ m + 2 ∈ S := by
  constructor
  · by_contra hnot
    have hsub :
        S ⊆ {m, m + 2, m + 3} := by
      intro q hq
      have hb := hbounds q hq
      have hne : q ≠ m + 1 := by
        simpa using hnot
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hc := Finset.card_le_card hsub
    rw [hcard] at hc
    norm_num at hc
  · by_contra hnot
    have hsub :
        S ⊆ {m, m + 1, m + 3} := by
      intro q hq
      have hb := hbounds q hq
      have hne : q ≠ m + 2 := by
        simpa using hnot
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hc := Finset.card_le_card hsub
    rw [hcard] at hc
    norm_num at hc

#print axioms finset_card_four_interval_three_inner_mem

end JSP000404Research
