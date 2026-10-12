import JSP000404Research.ResidualIncomparableBridgeCodimension
import JSP000404Research.ResidualBridgeReverseLowerDyadicBudget
import Mathlib.Tactic

/-!
# Incomparable bridge mass is <= half the SATURATED strict-rigid lower target

For the original candidate bridge (b,v), b is the lower endpoint of
some NET strict-descent rigid hard carrier q=(b,z). Under the existing
one-layer exponent/active budget, the kernel already proves the exact
saturation identity

  projectedFree(b) = exponent(b).

Actual forward/reverse collision bridge candidates are now filtered by
incomparable retained-active endpoint palettes. This guarantees an
active coordinate at v that is NOT active at b, hence the bridge
overlap cube has at least one less free coordinate than Q_b.

Combining the proven saturation and incomparable-palette witness:

  card(commonRetainedInactive(b,v)) + 1 <= exponent(b).

This yields the sharpened bridge mass bound:

  2 * 2^card(commonInactive(b,v)) <= 2^exponent(b).

Unlike a global ambient 2^(n-2) bound, this is expressed DIRECTLY in
the strict descent lower-target dyadic currency of the unsolved
six-source payment. Do not mistake this covered-word inequality for
the missing true-hole / unreserved-surplus budget.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Incomparable potential bridges have at least one FEWER free
coordinate than their own reverse strict-rigid saturated lower target.
This is an exact local strict-target exponent statement. -/
theorem incomparable_bridge_common_inactive_lt_strict_lower_exponent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (r : V × V)
    (hr : r ∈ incomparableBridgeSoftCarriers C exponent) :
    (commonRetainedInactive C r.1 r.2).card + 1 ≤ exponent r.1 := by
  classical
  have hinc := (Finset.mem_filter.mp hr).2
  have hdim := (common_inactive_card_plus_each_active_lt_n
    C r.1 r.2 hinc).1
  have hcan : r ∈ forwardReverseBridgeSoftCarriers C exponent :=
    (Finset.mem_filter.mp hr).1
  have hdata := (Finset.mem_filter.mp hcan).2
  obtain ⟨p, hp, q, hq, hlower, _hupper⟩ := hdata
  have hsat :=
    netStrictRigidLower_projectedFree_eq_exponent
      C exponent hexp honeLoss hq
  change n - (retainedActive C q.1).card = exponent q.1 at hsat
  have hsat' : n - (retainedActive C r.1).card =
      exponent r.1 := by
    simpa only [hlower] using hsat
  omega

/-- A filtered candidate bridge has at most HALF of the dyadic mass
of its own associated lower-target cube. There is no double counting
of distinct bridge words here; this is an individual-face estimate. -/
theorem incomparable_bridge_face_twice_mass_le_strict_lower_target
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (r : V × V)
    (hr : r ∈ incomparableBridgeSoftCarriers C exponent) :
    2 * (2 ^ (commonRetainedInactive C r.1 r.2).card) ≤
      2 ^ exponent r.1 := by
  have hdim :=
    incomparable_bridge_common_inactive_lt_strict_lower_exponent
      C exponent hexp honeLoss r hr
  have hpow :
      2 ^ ((commonRetainedInactive C r.1 r.2).card + 1) ≤
        2 ^ exponent r.1 :=
    pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hdim
  simpa [pow_succ, Nat.mul_comm] using hpow

/-- Every eligible bridge lower-target exponent must be positive:
zero-dimensional reverse lower target cannot support a
palette-incomparable opposite hard collision bridge. -/
theorem incomparable_bridge_lower_exponent_positive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (r : V × V)
    (hr : r ∈ incomparableBridgeSoftCarriers C exponent) :
    0 < exponent r.1 := by
  have hdim :=
    incomparable_bridge_common_inactive_lt_strict_lower_exponent
      C exponent hexp honeLoss r hr
  omega

/-- A dimension-aware GLOBAL bridge estimate with the dyadic
lower-target exponent of EACH actual oriented candidate bridge,
instead of the ambient n or an unweighted bridge carrier count.
Repeated lower endpoints remain repeated in the SUM; they are
NOT assumed to be disjoint payments of profile surplus. -/
theorem incomparable_bridge_twice_mass_le_sum_lower_target
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    2 * (incomparableBridgeSoftWords C exponent).card ≤
      ∑ r ∈ incomparableBridgeSoftCarriers C exponent,
        2 ^ exponent r.1 := by
  classical
  rw [incomparable_bridge_soft_words_card_eq_dyadic_sum]
  have hsum :
      (∑ r ∈ incomparableBridgeSoftCarriers C exponent,
        2 * 2 ^ (commonRetainedInactive C r.1 r.2).card) ≤
      ∑ r ∈ incomparableBridgeSoftCarriers C exponent,
        2 ^ exponent r.1 := by
    apply Finset.sum_le_sum
    intro r hr
    exact incomparable_bridge_face_twice_mass_le_strict_lower_target
      C exponent hexp honeLoss r hr
  simpa only [Finset.mul_sum] using hsum

/-- The actual NET unpaid forward/reverse collision duplication is
also bounded by half of the lower-target mass, COUNTING EVERY
surviving oriented soft bridge exactly once (not every word twice). -/
theorem net_actual_collision_twice_le_sum_bridge_lower_targets
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    2 * (netActualForwardReverseCollisionWords
      C exponent hexp honeLoss).card ≤
      ∑ r ∈ incomparableBridgeSoftCarriers C exponent,
        2 ^ exponent r.1 := by
  have hsub :=
    net_actual_collision_card_le_incomparable_bridge_mass
      C exponent hexp honeLoss
  have hmass :=
    incomparable_bridge_twice_mass_le_sum_lower_target
      C exponent hexp honeLoss
  omega

#print axioms incomparable_bridge_common_inactive_lt_strict_lower_exponent
#print axioms incomparable_bridge_face_twice_mass_le_strict_lower_target
#print axioms incomparable_bridge_lower_exponent_positive
#print axioms incomparable_bridge_twice_mass_le_sum_lower_target
#print axioms net_actual_collision_twice_le_sum_bridge_lower_targets

end OrderedEdgeColoring
end JSP000404Research
