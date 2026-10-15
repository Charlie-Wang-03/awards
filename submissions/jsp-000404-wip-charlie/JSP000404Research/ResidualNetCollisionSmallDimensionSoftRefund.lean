import JSP000404Research.ResidualNetCollisionActualSourceShadowDichotomy
import Mathlib.Tactic

/-!
# An unconditional small-dimensional NET first-hit SOFT refund

The previous actual-source obstruction classified any shortage of distinct
SOFT overlap words into a two-bit target pair with an additional unique
outside-coordinate pivot, or a four-bit target pair.

Both structures require at least three Boolean coordinates. Hence, when
n <= 2, the ACTUAL certified NET first-hit plus duplicate incidence debt
is paid by distinct real SOFT overlap words, without introducing any
unproved target-separation or geometry hypothesis.

This is an unconditional genuine NET subcase, not a six-source proof:
SOFT words remain COVERED, never true Boolean holes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- An actual NET first-hit SOFT-credit shortfall forces n >= 3,
because its certified two-target collision carries either an
outside pivot in addition to two differing bits, or four bits. -/
theorem net_first_hit_soft_shortage_forces_three_colours
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hfail :
      (softOverlapCompletionWords C).card <
        netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
          (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card) :
    3 ≤ n := by
  classical
  obtain ⟨s, hs, w₁, w₂, hne, hA, hB, hcase⟩ :=
    net_first_hit_shortage_actual_source_unique_pivot_or_disjoint
      C exponent hexp honeLoss hfail
  let d := netCollisionCertifiedDiagonal C exponent hexp honeLoss w₁
  let e := netCollisionCertifiedDiagonal C exponent hexp honeLoss w₂
  let T : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => d i ≠ e i)
  rcases hcase with ⟨hT2, hpivot⟩ | ⟨hT4, _⟩
  · obtain ⟨pivot, hp, _⟩ := hpivot
    have hpnot : pivot ∉ T := by
      intro hmem
      have hdiff : d pivot ≠ e pivot :=
        (Finset.mem_filter.mp hmem).2
      exact hdiff hp.2.2
    have hins : (insert pivot T).card = 3 := by
      rw [Finset.card_insert_of_not_mem hpnot, hT2]
    have hbound : (insert pivot T).card ≤ n := by
      have hsub : insert pivot T ⊆ (Finset.univ : Finset (Fin n)) :=
        Finset.subset_univ _
      simpa using Finset.card_le_card hsub
    omega
  · have hbound : T.card ≤ n := by
      have hsub : T ⊆ (Finset.univ : Finset (Fin n)) :=
        Finset.subset_univ _
      simpa using Finset.card_le_card hsub
    omega

/-- For <=2 retained Boolean coordinates, actual NET first hits
and their genuine duplicate debt are bounded by distinct SOFT words. -/
theorem net_first_hits_plus_duplicates_le_actual_soft_of_n_le_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hn : n ≤ 2) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
      (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card ≤
        (softOverlapCompletionWords C).card := by
  by_contra hnot
  have hfail :
      (softOverlapCompletionWords C).card <
        netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
          (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card :=
    Nat.lt_of_not_ge hnot
  have hn3 :=
    net_first_hit_soft_shortage_forces_three_colours
      C exponent hexp honeLoss hfail
  omega

#print axioms net_first_hit_soft_shortage_forces_three_colours
#print axioms net_first_hits_plus_duplicates_le_actual_soft_of_n_le_two

end OrderedEdgeColoring
end JSP000404Research
