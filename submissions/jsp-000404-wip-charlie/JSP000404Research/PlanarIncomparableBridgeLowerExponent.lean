import JSP000404Research.PlanarNetActualCollisionPaymentFrontier
import JSP000404Research.ResidualIncomparableBridgeLowerExponent
import Mathlib.Tactic

/-!
# Actual planar AngleCap: bridge collision duplication versus strict lower targets

For real planar AngleCap data, the certified one-layer exponent/active
budgets and strict-rigid lower endpoint saturation imply:

  2 * (NET actual forward/reverse sink intersection mass)
    <= SUM_(palette-incomparable oriented bridge carrier r=(b,v))
         2^centreExponent(b).

This is a stronger LOCAL TARGET-RELATIVE restriction than the global
ambient 2^(n-2) bound; each eligible bridge cube has dimension strictly
less than its reverse strict lower endpoint's saturated exponent.

The sum here counts each candidate BRIDGE (not each distinct lower
endpoint) separately, so this is NOT yet a non-reusing sum of
independent dyadic profile payments or true holes.

No additional geometric hypothesis beyond the established AngleCap
and genuine projective centre cycles is introduced.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_net_actual_collision_twice_le_strict_lower_target_sum
    {V : Type*} [Fintype V] {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let htpos : 0 < t := by
      rw [ht]
      have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    let hwidth : t < (n : ℝ) + 1 := by rw [ht]; linarith
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D n (by exact_mod_cast hwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    ∃ (hexp : ∀ i : ProjectionOrdered V, k i ≤ n),
      ∃ (honeLoss : ∀ i : ProjectionOrdered V,
          (active B i).card ≤ n - k i + 1),
        2 * (netActualForwardReverseCollisionWords B k hexp honeLoss).card ≤
          ∑ r ∈ incomparableBridgeSoftCarriers B k, 2 ^ k r.1 := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by
    rw [ht]
    have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwidth : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hdelta1 : delta < 1 := by linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  have hexp : ∀ i : ProjectionOrdered V, k i ≤ n := by
    intro i
    exact Nat.le_of_lt
      (centreExponent_lt_n (cycles i) n delta t
        hn hdelta0 hdelta1 ht)
  have honeLoss :
      ∀ i : ProjectionOrdered V,
        (active B i).card ≤ n - k i + 1 := by
    intro i
    exact planarStandardResidual_active_card_le_oneLayer
      hp hcap hn hdelta0 hdelta1 ht hlam i (cycles i)
  change ∃ (hexp : ∀ i : ProjectionOrdered V, k i ≤ n),
    ∃ (honeLoss : ∀ i : ProjectionOrdered V,
        (active B i).card ≤ n - k i + 1),
      2 * (netActualForwardReverseCollisionWords B k hexp honeLoss).card ≤
          ∑ r ∈ incomparableBridgeSoftCarriers B k, 2 ^ k r.1
  exact ⟨hexp, honeLoss,
    net_actual_collision_twice_le_sum_bridge_lower_targets
      B k hexp honeLoss⟩

#print axioms planar_net_actual_collision_twice_le_strict_lower_target_sum

end ProjectionOrdered
end JSP000404Research
