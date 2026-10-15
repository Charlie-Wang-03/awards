import JSP000404Research.ResidualTwoShadowParityGate
import JSP000404Research.ResidualNetCollisionShadowFirstHitGlobalCharge
import Mathlib.Tactic

/-!
# An actual reused SOFT witness for failed NET distinct-shadow payment

The old close-target dichotomy only certified that TWO attained NET
diagonals at distance 2 or 4 must exist when NET first-hit debt exceeds
the available number of SOFT shadow words. Here we additionally extract
one SINGLE ACTUAL SOFT overlap word s that simultaneously shadows those
two genuinely attained diagonals.

This is a necessary condition on a failed distinct-shadow payment, NOT
a genuine Boolean hole, unreserved dyadic credit, or proof that the
planar AngleCap hypothesis forbids the obstruction.
-/

namespace JSP000404Research

/-- If a finite degree sum exceeds its underlying support cardinality,
one actual support element necessarily has degree at least two. -/
theorem finite_degree_sum_gt_card_has_reused_support
    {α : Type*} [DecidableEq α]
    (S : Finset α) (deg : α → ℕ)
    (hlarge : S.card < ∑ s ∈ S, deg s) :
    ∃ s ∈ S, 2 ≤ deg s := by
  classical
  by_contra hnone
  have hone : ∀ s ∈ S, deg s ≤ 1 := by
    intro s hs
    by_contra h
    have htwo : 2 ≤ deg s := by omega
    exact hnone ⟨s, hs, htwo⟩
  have hle : (∑ s ∈ S, deg s) ≤ ∑ _s ∈ S, (1 : ℕ) := by
    apply Finset.sum_le_sum
    intro s hs
    exact hone s hs
  have hcard : (∑ _s ∈ S, (1 : ℕ)) = S.card := by simp
  omega

end JSP000404Research

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A genuinely failed distinct-SOFT payment forces one ACTUAL SOFT word
s which is at Hamming distance two from TWO DISTINCT, ACTUALLY ATTAINED
NET diagonals d,e, and their mutual distance is exactly two or four.

This strictly sharpens the previous existence of an unconnected close
target pair by explicitly certifying the overlapping paid resource. -/
theorem net_first_hit_shortage_forces_actual_shared_soft_witness
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hfail :
      (softOverlapCompletionWords C).card <
        netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
          (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card) :
    ∃ s ∈ softOverlapCompletionWords C,
      ∃ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
      ∃ e ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        d ≠ e ∧
        (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2 ∧
        (Finset.univ.filter (fun i : Fin n => s i ≠ e i)).card = 2 ∧
        ((Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card = 2 ∨
          (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card = 4) := by
  classical
  let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
  let S := softOverlapCompletionWords C
  let deg : (Fin n → Bool) → ℕ := fun s =>
    (D.filter (fun d =>
      (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card
  have hbase :=
    net_duplicate_plus_distinct_hits_le_soft_shadow_incidence
      C exponent hexp honeLoss
  change netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
    D.card ≤ ∑ s ∈ S, deg s at hbase
  have hstrict : S.card < ∑ s ∈ S, deg s := by
    change S.card <
      netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
        D.card at hfail
    omega
  obtain ⟨s, hs, htwo⟩ :=
    finite_degree_sum_gt_card_has_reused_support S deg hstrict
  have hpair :
      ∃ d ∈ D, ∃ e ∈ D,
        d ≠ e ∧
        (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2 ∧
        (Finset.univ.filter (fun i : Fin n => s i ≠ e i)).card = 2 := by
    by_contra hnone
    have hone :
        (D.filter (fun d =>
          (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro d hd e he
      by_contra hde
      have hd' := (Finset.mem_filter.mp hd)
      have he' := (Finset.mem_filter.mp he)
      exact hnone ⟨d, hd'.1, e, he'.1, hde, hd'.2, he'.2⟩
    change 2 ≤ (D.filter (fun d =>
      (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card at htwo
    omega
  obtain ⟨d, hd, e, he, hde, hsd, hse⟩ := hpair
  have hdist :=
    distinct_targets_of_shared_two_shadow_hamming_two_or_four
      s d e hsd hse hde
  exact ⟨s, hs, d, hd, e, he, hde, hsd, hse, hdist⟩

#print axioms finite_degree_sum_gt_card_has_reused_support
#print axioms net_first_hit_shortage_forces_actual_shared_soft_witness

end OrderedEdgeColoring
end JSP000404Research
