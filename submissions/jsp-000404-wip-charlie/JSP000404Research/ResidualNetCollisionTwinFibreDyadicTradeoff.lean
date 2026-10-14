import JSP000404Research.ResidualNetCollisionTwinAdjustedFibre
import Mathlib.Tactic

/-!
# Exact-fibre versus TWIN dyadic liability tradeoff

For every target diagonal d, ALL actual source hard-carrier pairs
and ALL terminal TWIN hard-carrier pairs inhabit the SAME global
original-centre matching.

When every exponent is strictly less than the Boolean dimension n:

  sum_(q in TWIN) 2^(k(q.upper)) <=
    (floor(|V|/2) - 2*|F_d|) * 2^(n-1).

This is a joint original-centre capacity constraint for EACH target,
not a sum of independent vertex payments across target fibres.
The result is an upper bound on a liability, NOT unreserved surplus.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem net_collision_twin_mass_le_fibre_adjusted_dyadic_budget
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hstrict : ∀ v, exponent v < n)
    (d : Fin n → Bool) :
    (∑ p ∈ netTwinRigidCarriers C exponent,
      (2 : ℕ) ^ exponent p.2) ≤
    (Fintype.card V / 2 -
      2 * (netCollisionCertifiedDiagonalFibre
        C exponent hexp honeLoss d).card) * (2 : ℕ) ^ (n - 1) := by
  classical
  let T := netTwinRigidCarriers C exponent
  let F := netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d
  have hvertex := net_collision_fibre_twin_joint_vertex_budget
    C exponent hexp honeLoss d
  have hcard : T.card ≤ Fintype.card V / 2 - 2 * F.card := by
    change 4 * F.card + 2 * T.card ≤ Fintype.card V at hvertex
    omega
  have hpow (p : V × V) :
      (2 : ℕ) ^ exponent p.2 ≤ (2 : ℕ) ^ (n - 1) := by
    have hlevel : exponent p.2 ≤ n - 1 := by
      have h := hstrict p.2
      omega
    exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hlevel
  change (∑ p ∈ T, (2 : ℕ) ^ exponent p.2) ≤
    (Fintype.card V / 2 - 2 * F.card) * (2 : ℕ) ^ (n - 1)
  calc
    (∑ p ∈ T, (2 : ℕ) ^ exponent p.2) ≤
      ∑ p ∈ T, (2 : ℕ) ^ (n - 1) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpow p
    _ = T.card * (2 : ℕ) ^ (n - 1) := by simp
    _ ≤ (Fintype.card V / 2 - 2 * F.card) * (2 : ℕ) ^ (n - 1) :=
      Nat.mul_le_mul_right ((2 : ℕ) ^ (n - 1)) hcard

/-- Two actual sources hitting the same target cap the entire TWIN
dyadic mass by the original four-pair reservation. -/
theorem net_collision_twin_mass_le_global_duplicate_budget_of_fibre_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hstrict : ∀ v, exponent v < n)
    (d : Fin n → Bool)
    (htwo : 2 ≤ (netCollisionCertifiedDiagonalFibre
      C exponent hexp honeLoss d).card) :
    (∑ p ∈ netTwinRigidCarriers C exponent,
      (2 : ℕ) ^ exponent p.2) ≤
    (Fintype.card V / 2 - 4) * (2 : ℕ) ^ (n - 1) := by
  have hmass := net_collision_twin_mass_le_fibre_adjusted_dyadic_budget
    C exponent hexp honeLoss hstrict d
  have hfactor :
      Fintype.card V / 2 -
        2 * (netCollisionCertifiedDiagonalFibre
          C exponent hexp honeLoss d).card ≤
      Fintype.card V / 2 - 4 := by
    omega
  exact hmass.trans
    (Nat.mul_le_mul_right ((2 : ℕ) ^ (n - 1)) hfactor)

#print axioms net_collision_twin_mass_le_fibre_adjusted_dyadic_budget
#print axioms net_collision_twin_mass_le_global_duplicate_budget_of_fibre_two

end OrderedEdgeColoring
end JSP000404Research
