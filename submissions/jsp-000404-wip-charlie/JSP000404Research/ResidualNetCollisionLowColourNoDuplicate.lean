import JSP000404Research.ResidualNetCollisionLocalSoftSphereCapacity
import Mathlib.Tactic

/-!
# Low-colour proof closure of the ACTUAL NET duplicate-image debt

A genuine same-target NET collision fibre injects into the unordered
2-element subsets of the retained n colours. For n<=2 there is AT
MOST ONE two-element subset; hence its canonical opposite-diagonal
target map is genuinely globally injective and its duplicate-image
debt is EXACTLY ZERO.

The n<=1 emptiness fact was ALREADY formally present in the
repository, so it is deliberately NOT redeclared here.

This is an unconditional small-colour elimination of one specific
geometric accounting debt under only the pre-existing one-layer
budget. The COVERED diagonal blocker debit, twin rigid, mixed-rigid,
soft-overlap mass, and projected loss are NOT removed, so this is
NOT a full sharp planar lower-branch solution for n<=2.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- With at most TWO retained colours, a genuine NET source-target
diagonal fibre contains at most ONE source. The previous choose-two
bound now has a numerical (nonconditional) sharp consequence. -/
theorem net_collision_target_fibre_card_le_one_of_n_le_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hn : n ≤ 2) (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre
      C exponent hexp honeLoss d).card ≤ 1 := by
  have hbound :=
    net_collision_fixed_diagonal_fibre_card_le_choose_two
      C exponent hexp honeLoss d
  change
    (netCollisionCertifiedDiagonalFibre
      C exponent hexp honeLoss d).card ≤ Nat.choose n 2 at hbound
  have hchoose : Nat.choose n 2 ≤ 1 := by
    interval_cases n <;> norm_num at *
  omega

/-- In dimension n<=2, the CANONICAL genuine NET collision
diagonal map is injective across ALL true collision sink words.
This proof uses actual finite source fibre cardinality, not
an unproved AngleCap geometric matching exclusion. -/
theorem net_collision_certified_diagonal_injective_of_n_le_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hn : n ≤ 2) :
    Function.Injective
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss) := by
  classical
  intro s t hst
  let d := netCollisionCertifiedDiagonal C exponent hexp honeLoss s
  let F := netCollisionCertifiedDiagonalFibre
    C exponent hexp honeLoss d
  have hs : s ∈ F := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, rfl⟩
  have ht : t ∈ F := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hst.symm⟩
  have hcard : F.card ≤ 1 :=
    net_collision_target_fibre_card_le_one_of_n_le_two
      C exponent hexp honeLoss hn d
  exact (Finset.card_le_one.mp hcard) s hs t ht

/-- The exact duplicate-image debt is UNCONDITIONALLY zero
whenever n<=2. This removes the entire repeated canonical
hole-target charge from the small-colour NET ledger. -/
theorem net_collision_duplicate_debt_zero_of_n_le_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hn : n ≤ 2) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss = 0 := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_eq_zero
  intro d hd
  have hf :=
    net_collision_target_fibre_card_le_one_of_n_le_two
      C exponent hexp honeLoss hn d
  omega

/-- The genuine two-mobile-source ledger now has NO
multiple-hit term in the n<=2 regime. The DISTINCT covered
diagonals remain explicitly separated from TRUE Boolean holes;
other global dyadic debts have not been paid. -/
theorem net_mobile_mass_le_holes_covered_without_duplicates_of_n_le_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hn : n ≤ 2) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
      (softOverlapCompletionWords C).card +
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card +
      (netCollisionCertifiedCoveredDiagonals
        C exponent hexp honeLoss).card := by
  have hmobile :=
    net_mobile_mass_le_singleton_soft_holes_blockers_duplicates
      C exponent hexp honeLoss
  have hzero :=
    net_collision_duplicate_debt_zero_of_n_le_two
      C exponent hexp honeLoss hn
  omega

#print axioms net_collision_target_fibre_card_le_one_of_n_le_two
#print axioms net_collision_certified_diagonal_injective_of_n_le_two
#print axioms net_collision_duplicate_debt_zero_of_n_le_two
#print axioms net_mobile_mass_le_holes_covered_without_duplicates_of_n_le_two

end OrderedEdgeColoring
end JSP000404Research
