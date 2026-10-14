import JSP000404Research.ResidualNetCollisionElevenCentreTwinCap
import Mathlib.Tactic

/-!
# A strictly bounded dyadic TWIN bill in the eleven-centre regime

This is a *liability bound*, NOT a transfer of payment. If genuine NET
diagonal duplication is positive and there are at most eleven centres,
at most one equal-exponent TWIN hard carrier survives. If each exponent
is strictly below the Boolean dimension n, its entire TWIN dyadic mass
is at most 2^(n-1).

The all-centre AngleCap hypotheses establish strict exponent bound via
centreExponent_lt_n; this lemma does not assume any free Boolean hole.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem net_collision_positive_duplicate_eleven_centres_twin_mass_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hstrict : ∀ v, exponent v < n)
    (hsmall : Fintype.card V ≤ 11)
    (hpositive : 0 < netCollisionCertifiedDuplicateDebt
      C exponent hexp honeLoss) :
    (∑ p ∈ netTwinRigidCarriers C exponent, (2 : ℕ) ^ exponent p.2) ≤
      (2 : ℕ) ^ (n - 1) := by
  classical
  let T := netTwinRigidCarriers C exponent
  have hcard : T.card ≤ 1 :=
    net_collision_positive_duplicate_eleven_centres_twin_card_le_one
      C exponent hexp honeLoss hsmall hpositive
  have hpow (p : V × V) :
      (2 : ℕ) ^ exponent p.2 ≤ (2 : ℕ) ^ (n - 1) := by
    have he : exponent p.2 ≤ n - 1 := by
      have hp := hstrict p.2
      omega
    exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) he
  change (∑ p ∈ T, (2 : ℕ) ^ exponent p.2) ≤ (2 : ℕ) ^ (n - 1)
  calc
    (∑ p ∈ T, (2 : ℕ) ^ exponent p.2) ≤
        ∑ p ∈ T, (2 : ℕ) ^ (n - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hpow p
    _ = T.card * (2 : ℕ) ^ (n - 1) := by simp
    _ ≤ 1 * (2 : ℕ) ^ (n - 1) :=
      Nat.mul_le_mul_right ((2 : ℕ) ^ (n - 1)) hcard
    _ = (2 : ℕ) ^ (n - 1) := by simp

#print axioms net_collision_positive_duplicate_eleven_centres_twin_mass_le

end OrderedEdgeColoring
end JSP000404Research
