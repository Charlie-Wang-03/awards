import JSP000404Research.ResidualNetCollisionShadowFirstHitGlobalCharge
import JSP000404Research.ResidualNetCollisionCertifiedMobilePayment
import Mathlib.Tactic

/-!
# Non-reused true-hole refund against global SOFT shadow incidence

The old genuine NET mobile hard-source ledger includes:
  global true holes + distinct COVERED diagonal blockers + duplicate debt.
The newly verified first-hit SOFT-shadow capacity controls:
  duplicate debt + ALL distinct actually hit diagonals.

Because every hit diagonal is EITHER a true hole OR covered,
the two ledgers can be combined while cancelling the covered blockers
and EXCLUDING the true holes already consumed as NET diagonals.

Result: mobile mass <= singleton + soft + (ALL holes minus NET-hit
true holes) + global target-shadow SOFT incidence multiplicity.

The remaining incidence multiplicity involves already-COVERED SOFT
words and remains UNPAID. This is NOT a global six-source theorem.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Exact original true-hole / already-covered partition of
the DISTINCT ACTUAL NET target diagonals. -/
theorem net_collision_distinct_targets_eq_true_holes_add_covered
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card =
      (netCollisionCertifiedTrueHoleDiagonals
        C exponent hexp honeLoss).card +
      (netCollisionCertifiedCoveredDiagonals
        C exponent hexp honeLoss).card := by
  classical
  let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
  let K := coveredCompletionWords C
  let H := (Finset.univ : Finset (Fin n → Bool)) \ K
  have hpart : D = (D ∩ H) ∪ (D ∩ K) := by
    ext d
    by_cases hd : d ∈ K <;> simp [H, hd]
  have hdisj : Disjoint (D ∩ H) (D ∩ K) := by
    apply Finset.disjoint_left.mpr
    intro d hdH hdK
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hdH).2).2
      (Finset.mem_inter.mp hdK).2
  have hsum : D.card = (D ∩ H).card + (D ∩ K).card := by
    calc
      D.card = ((D ∩ H) ∪ (D ∩ K)).card := by rw [← hpart]
      _ = (D ∩ H).card + (D ∩ K).card :=
        Finset.card_union_of_disjoint hdisj
  simpa only [D, H, K, netCollisionCertifiedTrueHoleDiagonals,
    netCollisionCertifiedCoveredDiagonals] using hsum

/-- The old mobile ledger can refund TRUE holes that are ALREADY
charged to distinct actual NET targets. The COVERED diagonal terms
also cancel, but SOFT shadow incidence reuse is NOT free payment. -/
theorem net_mobile_mass_le_unhit_true_holes_plus_global_soft_incidence
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
      (softOverlapCompletionWords C).card +
      (((Finset.univ : Finset (Fin n → Bool)) \
          coveredCompletionWords C).card -
        (netCollisionCertifiedTrueHoleDiagonals
          C exponent hexp honeLoss).card) +
      (∑ s ∈ softOverlapCompletionWords C,
        ((netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).filter
          (fun d =>
            (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card) := by
  classical
  let Holes := (Finset.univ : Finset (Fin n → Bool)) \
    coveredCompletionWords C
  let HD := netCollisionCertifiedTrueHoleDiagonals
    C exponent hexp honeLoss
  have hmobile := net_mobile_mass_le_singleton_soft_holes_blockers_duplicates
    C exponent hexp honeLoss
  have hincidence := net_duplicate_plus_distinct_hits_le_soft_shadow_incidence
    C exponent hexp honeLoss
  have hsplit := net_collision_distinct_targets_eq_true_holes_add_covered
    C exponent hexp honeLoss
  have hsubset : HD.card ≤ Holes.card := by
    apply Finset.card_le_card
    intro d hd
    exact (Finset.mem_inter.mp hd).2
  change (netTransportableHardWords C exponent).card +
    (netStrictDescentRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
      (softOverlapCompletionWords C).card +
      (Holes.card - HD.card) +
      (∑ s ∈ softOverlapCompletionWords C,
        ((netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).filter
          (fun d =>
            (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card)
  omega

#print axioms net_collision_distinct_targets_eq_true_holes_add_covered
#print axioms net_mobile_mass_le_unhit_true_holes_plus_global_soft_incidence

end OrderedEdgeColoring
end JSP000404Research
