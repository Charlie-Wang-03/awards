import JSP000404Research.ResidualNetCollisionShadowFirstUseReuseDefect
import JSP000404Research.ResidualNetCollisionShadowReuseMultiplicityCap
import Mathlib.Tactic

/-!
# Reused-shadow support, not all SOFT words, pays multiplicity

An actual SOFT shadow word s is "reused" only when it shadows at least
two distinct attained NET diagonals. The exact extra-use debt is zero
outside this set. A single word can be incident to at most choose(n,2)
distinct two-bit targets.

This refines the prior full-SOFT-inventory multiplicity estimate without
identifying covered SOFT words with true Boolean holes or independent
unreserved dyadic surplus. The unrestricted six-source geometric payment
obligation remains open.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The multiplicity defect is supported only on degree-at-least-two items. -/
theorem finite_degree_reuse_le_support_card_mul
    {α : Type*} [DecidableEq α]
    (S : Finset α) (deg : α → ℕ) (cap : ℕ)
    (hcap : ∀ s ∈ S, deg s ≤ cap) :
    (∑ s ∈ S, (deg s - 1)) ≤
      (S.filter (fun s => 1 < deg s)).card * (cap - 1) := by
  classical
  have hfilter :
      (∑ s ∈ S, (deg s - 1)) =
        ∑ s ∈ S.filter (fun s => 1 < deg s), (deg s - 1) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases h : 1 < deg s
    · simp [h]
    · have hz : deg s - 1 = 0 := by omega
      simp [h, hz]
  rw [hfilter]
  calc
    (∑ s ∈ S.filter (fun s => 1 < deg s), (deg s - 1)) ≤
        ∑ _s ∈ S.filter (fun s => 1 < deg s), (cap - 1) := by
      apply Finset.sum_le_sum
      intro s hs
      exact Nat.sub_le_sub_right (hcap s (Finset.mem_filter.mp hs).1) 1
    _ = (S.filter (fun s => 1 < deg s)).card * (cap - 1) := by simp

/-- Exact first-hit NET debt is bounded by distinct first-use SOFT words
plus at most (choose(n,2)-1) extra uses for each genuinely reused SOFT word.
The RHS counts only the SUPPORT of cross-target reuse, not the entire
inventory of SOFT words. -/
theorem net_duplicate_first_hits_le_used_soft_plus_reused_support
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
    let S := softOverlapCompletionWords C
    let deg : (Fin n → Bool) → ℕ := fun s =>
      (D.filter (fun d =>
        (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss + D.card ≤
      (S.filter (fun s => 0 < deg s)).card +
        (S.filter (fun s => 1 < deg s)).card * (Nat.choose n 2 - 1) := by
  classical
  let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
  let S := softOverlapCompletionWords C
  let deg : (Fin n → Bool) → ℕ := fun s =>
    (D.filter (fun d =>
      (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card
  have hbudget :=
    net_duplicate_first_hits_le_used_soft_plus_reuse_defect
      C exponent hexp honeLoss
  have hdegree : ∀ s ∈ S, deg s ≤ Nat.choose n 2 := by
    intro s hs
    exact hamming_two_targets_card_le_choose D s
  have hreuse := finite_degree_reuse_le_support_card_mul
    S deg (Nat.choose n 2) hdegree
  change netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss + D.card ≤
    (S.filter (fun s => 0 < deg s)).card +
      ∑ s ∈ S, (deg s - 1) at hbudget
  change (∑ s ∈ S, (deg s - 1)) ≤
    (S.filter (fun s => 1 < deg s)).card * (Nat.choose n 2 - 1) at hreuse
  exact hbudget.trans (Nat.add_le_add_left hreuse _)

/-- For at most two retained Boolean coordinates, distance-two shadow
incidence is automatically non-reusing, even if multiple NET targets
are attained. This removes the extra singleton-target assumption. -/
theorem net_duplicate_first_hits_le_soft_words_of_small_dimension
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hn : n ≤ 2) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
      (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card ≤
        (softOverlapCompletionWords C).card := by
  classical
  apply net_duplicate_first_hits_le_soft_words_of_no_cross_target_reuse
    C exponent hexp honeLoss
  intro s hs
  have hcap : Nat.choose n 2 ≤ 1 := by
    interval_cases n <;> decide
  exact (hamming_two_targets_card_le_choose
    (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss) s).trans hcap

#print axioms finite_degree_reuse_le_support_card_mul
#print axioms net_duplicate_first_hits_le_used_soft_plus_reused_support
#print axioms net_duplicate_first_hits_le_soft_words_of_small_dimension

end OrderedEdgeColoring
end JSP000404Research
