import JSP000404Research.PlanarLowerBranchTerminalTwinNetReduction
import JSP000404Research.ResidualBridgeStrictDyadicDescentGap
import Mathlib.Tactic

/-!
# Genuine planar sharp-centre STRICT DIMENSION DESCENT collision budget

The exact oriented SOFT bridge mass (an upper bound for all possible
forward/reverse sink collisions) is not an independent charge:
it must fit into the UNUSED lower-vs-upper completion cube capacity
of the strict-descending terminal rigid hard carriers.

Under the actual AngleCap one-layer residual profile, the dyadic sum
of candidate bridge faces is at most

    SUM_strict 2 ^ centreExponent(lower)
  - SUM_strict 2 ^ centreExponent(upper).

This comes from the certified abstract theorem and TRUE planar
one-layer active-card budgeting, without ANY new unproved Hall axiom.
The resulting gap is NOT automatically unreserved dyadic PROFILE
surplus (both rigid endpoints remain locally saturated), and is
NOT by itself a true-hole payment for the JSP lower branch.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_bridge_soft_dyadic_mass_le_strict_target_descent_gap
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
    (∑ e ∈ forwardReverseBridgeSoftCarriers B k,
      2 ^ (commonRetainedInactive B e.1 e.2).card) ≤
      (∑ q ∈ netStrictDescentRigidCarriers B k, 2 ^ k q.1) -
      (∑ q ∈ netStrictDescentRigidCarriers B k, 2 ^ k q.2) := by
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
  change (∑ e ∈ forwardReverseBridgeSoftCarriers B k,
      2 ^ (commonRetainedInactive B e.1 e.2).card) ≤
      (∑ q ∈ netStrictDescentRigidCarriers B k, 2 ^ k q.1) -
      (∑ q ∈ netStrictDescentRigidCarriers B k, 2 ^ k q.2)
  exact bridge_soft_dyadic_carrier_mass_le_strict_target_gap
    B k hexp honeLoss

#print axioms planar_bridge_soft_dyadic_mass_le_strict_target_descent_gap

end ProjectionOrdered
end JSP000404Research
