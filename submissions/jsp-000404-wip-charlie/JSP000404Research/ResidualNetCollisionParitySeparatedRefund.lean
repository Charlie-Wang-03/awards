import JSP000404Research.ResidualTwoShadowParityGate
import JSP000404Research.ResidualNetCollisionShadowFirstHitGlobalCharge
import Mathlib.Tactic

/-!
# Parity-sharp conditional NET first-hit / SOFT shadow refund

A SOFT shadow word s at distance two from TWO DISTINCT actual
NET diagonal targets d,e forces d_H(d,e) = 2 or 4.
Therefore avoiding only these TWO exact target-pair distances
is sufficient for a global no-cross-target-reuse bound.
This improves the older condition d_H(d,e) > 4, because distances
1 and 3 between targets are harmless as well.

The separation premise is NOT proved from planar AngleCap, and covered
SOFT words are NOT thereby converted into true Boolean holes or
unreserved profile credits. The full six-source payment is open.
-/

namespace JSP000404Research

/-- Pairwise exclusion of mutual target distances TWO and FOUR
makes every Hamming-two shadow adjacent to at most one target. -/
theorem no_two_four_separated_targets_shadow_degree_le_one
    {n : ℕ} (D : Finset (Fin n → Bool))
    (hsep : ∀ d ∈ D, ∀ e ∈ D, d ≠ e →
       (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card ≠ 2 ∧
       (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card ≠ 4)
    (s : Fin n → Bool) :
    (D.filter (fun d =>
      (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro d hd e he
  by_contra hde
  have hD : d ∈ D := (Finset.mem_filter.mp hd).1
  have hE : e ∈ D := (Finset.mem_filter.mp he).1
  have hds : (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2 :=
    (Finset.mem_filter.mp hd).2
  have hes : (Finset.univ.filter (fun i : Fin n => s i ≠ e i)).card = 2 :=
    (Finset.mem_filter.mp he).2
  obtain ⟨hnot2, hnot4⟩ := hsep d hD e hE hde
  rcases distinct_targets_of_shared_two_shadow_hamming_two_or_four
      s d e hds hes hde with h2 | h4
  · exact hnot2 h2
  · exact hnot4 h4

end JSP000404Research

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Stronger conditional global NET first-hit payment. It suffices that
distinct actual NET targets do not differ on exactly 2 or 4 bits.
This is weaker than the previously verified >4 separation hypothesis. -/
theorem net_first_hits_plus_duplicates_le_soft_of_no_two_four_target_pairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hsep :
      ∀ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
      ∀ e ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        d ≠ e →
          (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card ≠ 2 ∧
          (Finset.univ.filter (fun i : Fin n => d i ≠ e i)).card ≠ 4) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
      (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card ≤
        (softOverlapCompletionWords C).card := by
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
  have hone : ∀ s ∈ S, deg s ≤ 1 := by
    intro s hs
    exact no_two_four_separated_targets_shadow_degree_le_one D hsep s
  calc
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
        D.card ≤ ∑ s ∈ S, deg s := hbase
    _ ≤ ∑ _s ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro s hs
      exact hone s hs
    _ = S.card := by simp

#print axioms net_first_hits_plus_duplicates_le_soft_of_no_two_four_target_pairs

end OrderedEdgeColoring

#print axioms no_two_four_separated_targets_shadow_degree_le_one

end JSP000404Research
