import JSP000404Research.ResidualNetCollisionExactFibreDebt
import JSP000404Research.ResidualNetCollisionCertifiedMobilePayment
import Mathlib.Tactic

/-!
# Exact global NET mobile payment with honest hole/covered fibre excess

The canonical duplicate-image debt has now been completely expressed
as the sum of excess cardinalities of genuine ACTUAL collision fibres.

We partition those exact local excesses by whether the corresponding
canonical diagonal d is a TRUE globally uncovered Boolean hole or
an ALREADY COVERED completion word. Neither family is counted twice.

Combining the partition with certified NET mobile-source conservation
gives an exact six-term payable/unpayable ledger without a mysterious
global duplicate constant. Planar exclusion/payment of the
source-side/fifth-centre blockers and repeated hole fibres is OPEN.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A generic disjoint partition of a finite weighted sum into
members lying in an arbitrary covered set K and its complement. -/
theorem finset_sum_split_covered_complement
    {α : Type*} [DecidableEq α]
    (D K : Finset α) (g : α → ℕ) :
    (∑ d ∈ D, g d) =
      (∑ d ∈ D ∩ ((Finset.univ : Finset α) \ K), g d) +
      (∑ d ∈ D ∩ K, g d) := by
  classical
  let H := (Finset.univ : Finset α) \ K
  have hpart : D = (D ∩ H) ∪ (D ∩ K) := by
    ext d
    by_cases hd : d ∈ K <;> simp [H, hd]
  have hdisj : Disjoint (D ∩ H) (D ∩ K) := by
    apply Finset.disjoint_left.mpr
    intro d hH hK
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hH).2).2
      (Finset.mem_inter.mp hK).2
  change (∑ d ∈ D, g d) =
    (∑ d ∈ D ∩ H, g d) + (∑ d ∈ D ∩ K, g d)
  calc
    (∑ d ∈ D, g d) =
        ∑ d ∈ (D ∩ H) ∪ (D ∩ K), g d := by rw [← hpart]
    _ = (∑ d ∈ D ∩ H, g d) + (∑ d ∈ D ∩ K, g d) :=
      Finset.sum_union hdisj

/-- Every individual unit of actual canonical duplicate debt
belongs to a concrete TRUE-HOLE-target fibre or to an ALREADY
COVERED-target fibre; the global excess is exactly their sum.
Neither the uncovered target nor covered target may be reused
as a fresh, distinct new hole to pay for extra sources. -/
theorem net_collision_certified_duplicate_debt_eq_hole_covered_fibre_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss =
      (∑ d ∈ netCollisionCertifiedTrueHoleDiagonals
          C exponent hexp honeLoss,
        ((netCollisionCertifiedDiagonalFibre
          C exponent hexp honeLoss d).card - 1)) +
      (∑ d ∈ netCollisionCertifiedCoveredDiagonals
          C exponent hexp honeLoss,
        ((netCollisionCertifiedDiagonalFibre
          C exponent hexp honeLoss d).card - 1)) := by
  classical
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  simpa only [netCollisionCertifiedTrueHoleDiagonals,
      netCollisionCertifiedCoveredDiagonals] using
    (finset_sum_split_covered_complement
      (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss)
      (coveredCompletionWords C)
      (fun d => (netCollisionCertifiedDiagonalFibre
        C exponent hexp honeLoss d).card - 1))

/-- Final exact NET mobile-source identity in literally distinct TRUE
hole targets, literally distinct COVERED targets, and the two
separately classified extra-source fibre debts. No covered word
is called a hole; duplicate uses of one true hole are NOT paid
by naming that hole again. -/
theorem net_mobile_source_plus_unused_eq_truehole_covered_fibre_accounting
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card +
      (netMobileUnusedCoveredSinkWords
        C exponent hexp honeLoss).card =
      (singletonCompletionWords C).card +
      (softOverlapCompletionWords C).card +
      (netCollisionCertifiedTrueHoleDiagonals
        C exponent hexp honeLoss).card +
      (netCollisionCertifiedCoveredDiagonals
        C exponent hexp honeLoss).card +
      (∑ d ∈ netCollisionCertifiedTrueHoleDiagonals
          C exponent hexp honeLoss,
        ((netCollisionCertifiedDiagonalFibre
          C exponent hexp honeLoss d).card - 1)) +
      (∑ d ∈ netCollisionCertifiedCoveredDiagonals
          C exponent hexp honeLoss,
        ((netCollisionCertifiedDiagonalFibre
          C exponent hexp honeLoss d).card - 1)) := by
  have h :=
    net_mobile_source_plus_unused_eq_certified_three_diagonals
      C exponent hexp honeLoss
  rw [net_collision_certified_duplicate_debt_eq_hole_covered_fibre_excess
    C exponent hexp honeLoss] at h
  exact h

#print axioms finset_sum_split_covered_complement
#print axioms net_collision_certified_duplicate_debt_eq_hole_covered_fibre_excess
#print axioms net_mobile_source_plus_unused_eq_truehole_covered_fibre_accounting

end OrderedEdgeColoring
end JSP000404Research
