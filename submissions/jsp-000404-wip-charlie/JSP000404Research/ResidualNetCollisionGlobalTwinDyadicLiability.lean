import JSP000404Research.ResidualNetCollisionTwinGlobalVertexBudget
import Mathlib.Tactic

/-!
# Unrestricted NET/TWIN dyadic liability upper bounds

A genuine duplicate target forces four additional HARD original-centre
pairs which are disjoint from every terminal TWIN pair. Therefore if
duplicate debt is positive, the number of TWIN hard carriers is at most
floor(|V| / 2) - 4, regardless of the number of original vertices.

This bounds the total TWIN dyadic liability when exponent < n, but
DOES NOT turn covered source targets into true Boolean holes and
DOES NOT supply an unreserved dyadic profile payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Universal dyadic TWIN debt cap with exponent bounded by n. -/
theorem net_collision_positive_duplicate_global_twin_mass_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hpositive : 0 < netCollisionCertifiedDuplicateDebt
      C exponent hexp honeLoss) :
    (∑ p ∈ netTwinRigidCarriers C exponent, (2 : ℕ) ^ exponent p.2) ≤
      (Fintype.card V / 2 - 4) * (2 : ℕ) ^ n := by
  classical
  let T := netTwinRigidCarriers C exponent
  have hbudget := net_collision_positive_duplicate_twin_card_plus_four_le_half
    C exponent hexp honeLoss hpositive
  have hcard : T.card ≤ Fintype.card V / 2 - 4 := by
    change T.card + 4 ≤ Fintype.card V / 2 at hbudget
    omega
  have hpow (p : V × V) :
      (2 : ℕ) ^ exponent p.2 ≤ (2 : ℕ) ^ n :=
    pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (hexp p.2)
  change (∑ p ∈ T, (2 : ℕ) ^ exponent p.2) ≤
    (Fintype.card V / 2 - 4) * (2 : ℕ) ^ n
  calc
    (∑ p ∈ T, (2 : ℕ) ^ exponent p.2) ≤
        ∑ p ∈ T, (2 : ℕ) ^ n := by
      apply Finset.sum_le_sum
      intro p hp
      exact hpow p
    _ = T.card * (2 : ℕ) ^ n := by simp
    _ ≤ (Fintype.card V / 2 - 4) * (2 : ℕ) ^ n :=
      Nat.mul_le_mul_right ((2 : ℕ) ^ n) hcard

/-- Strict exponents (as in planar AngleCap) halve the dyadic unit
upper bound and keep the original-centre budget unrestricted. -/
theorem net_collision_positive_duplicate_global_twin_mass_strict_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hstrict : ∀ v, exponent v < n)
    (hpositive : 0 < netCollisionCertifiedDuplicateDebt
      C exponent hexp honeLoss) :
    (∑ p ∈ netTwinRigidCarriers C exponent, (2 : ℕ) ^ exponent p.2) ≤
      (Fintype.card V / 2 - 4) * (2 : ℕ) ^ (n - 1) := by
  classical
  let T := netTwinRigidCarriers C exponent
  have hbudget := net_collision_positive_duplicate_twin_card_plus_four_le_half
    C exponent hexp honeLoss hpositive
  have hcard : T.card ≤ Fintype.card V / 2 - 4 := by
    change T.card + 4 ≤ Fintype.card V / 2 at hbudget
    omega
  have hpow (p : V × V) :
      (2 : ℕ) ^ exponent p.2 ≤ (2 : ℕ) ^ (n - 1) := by
    have hk : exponent p.2 ≤ n - 1 := by
      have hx := hstrict p.2
      omega
    exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hk
  change (∑ p ∈ T, (2 : ℕ) ^ exponent p.2) ≤
    (Fintype.card V / 2 - 4) * (2 : ℕ) ^ (n - 1)
  calc
    (∑ p ∈ T, (2 : ℕ) ^ exponent p.2) ≤
        ∑ p ∈ T, (2 : ℕ) ^ (n - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hpow p
    _ = T.card * (2 : ℕ) ^ (n - 1) := by simp
    _ ≤ (Fintype.card V / 2 - 4) * (2 : ℕ) ^ (n - 1) :=
      Nat.mul_le_mul_right ((2 : ℕ) ^ (n - 1)) hcard

/-- Explicit case split: either no actual duplicate debt, or the
strict TWIN dyadic liability is bounded by unused vertex-pair count. -/
theorem net_collision_duplicate_zero_or_global_twin_mass_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hstrict : ∀ v, exponent v < n) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss = 0 ∨
      (∑ p ∈ netTwinRigidCarriers C exponent,
        (2 : ℕ) ^ exponent p.2) ≤
          (Fintype.card V / 2 - 4) * (2 : ℕ) ^ (n - 1) := by
  by_cases h : netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss = 0
  · exact Or.inl h
  · exact Or.inr
      (net_collision_positive_duplicate_global_twin_mass_strict_le
        C exponent hexp honeLoss hstrict (Nat.pos_of_ne_zero h))

#print axioms net_collision_positive_duplicate_global_twin_mass_le
#print axioms net_collision_positive_duplicate_global_twin_mass_strict_le
#print axioms net_collision_duplicate_zero_or_global_twin_mass_le

end OrderedEdgeColoring
end JSP000404Research
