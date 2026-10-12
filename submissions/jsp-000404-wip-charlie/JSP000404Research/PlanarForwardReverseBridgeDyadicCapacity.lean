import JSP000404Research.PlanarLowerBranchTerminalTwinNetReduction
import JSP000404Research.ResidualForwardReverseBridgeDyadicMass
import Mathlib.Tactic

/-!
# Genuine planar sharp-centre specialization of the bridge-soft dyadic bound

The abstract two-direction forward/reverse transport theorem assumes
a one-layer projected active-card budget. The ACTUAL planar AngleCap
geometry and centre projective cycles certify this budget for the
standard residual colouring, with the exponent equal to
centreExponent(cycle_i,t).

Consequently, directly under the genuine lower-branch
0 <= delta < 1/2 assumptions, the STILL-UNPAID mobile hard
face mass is bounded by

  singletonCompletionWords
  + softOverlapCompletionWords
  + SUM_(oriented bridge soft edges e) 2^commonInactive(e).

This theorem uses actual planar input, not an arbitrary DirectionData
Hall axiom. It is SORRY-FREE, but NOT the actual global payment by
TRUE Boolean holes. AngleCap bounds angles from ABOVE (pi-lambda);
small angles between residual directions alone are not forbidden.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_mobile_hard_mass_le_singleton_soft_bridge_dyadic
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
    (netTransportableHardWords B k).card +
      (netStrictDescentRigidWords B k).card ≤
        (singletonCompletionWords B).card +
          (softOverlapCompletionWords B).card +
          (∑ e ∈ forwardReverseBridgeSoftCarriers B k,
            2 ^ (commonRetainedInactive B e.1 e.2).card) := by
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
  rw [← forwardReverseBridgeSoftWords_card_eq_dyadic_sum B k]
  exact net_forward_reverse_hard_mass_le_singleton_soft_bridge
    B k hexp honeLoss

#print axioms planar_mobile_hard_mass_le_singleton_soft_bridge_dyadic

end ProjectionOrdered
end JSP000404Research
