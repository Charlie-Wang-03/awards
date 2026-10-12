import JSP000404Research.PlanarLowerBranchBothMixedNetPaymentReduction
import JSP000404Research.ResidualTerminalHardNetPaymentReduction
import JSP000404Research.PlanarStandardResidualBudget
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Genuine planar bridge: exposed terminal rigid dyadic target debts

The only geometrically unproved input now has FIVE explicit sources:
soft overlap words; still-unpaid transportable hard words; full upper
target weights of terminal doubly-saturated rigid carriers; both mixed
rigid target masses; projected-profile losses.

The right hand side remains TRUE Boolean holes + total surplus after
the THREE already certified, non-reusing hard/mixed reservations.

The bridge derives the one-layer residual budget from actual AngleCap
geometry, then uses the new exact carrier-owned Boolean decomposition.
No new axioms, sorry, or unjustified hole injection are introduced.
The required global inequality remains unproved.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- The more granular true-plane net-payment inequality suffices to
establish the original lower-branch planar dyadic bound. -/
theorem planar_lower_branch_dyadic_capacity_of_terminal_hard_net_payment
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
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hterminal :
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
      (softOverlapCompletionWords B).card +
        (netTransportableHardWords B k).card +
        (∑ q ∈ netRigidHardCarriers B k, 2 ^ k q.2) +
        (∑ q ∈ ascendingUnpaidRigidCarriers B k, 2 ^ k q.1) +
        (∑ q ∈ descendingUnpaidRigidCarriers B k, 2 ^ k q.2) +
        totalDyadicProfileLoss k (projectedFree B) ≤
      (2 ^ n - (coveredCompletionWords B).card) +
        (totalDyadicProfileSurplus k (projectedFree B) -
          (surplusPaidHardOverlapWords B k).card -
          (∑ q ∈ ascendingUnpaidRigidCarriers B k,
            dyadicProfileSurplus k (projectedFree B) q.1) -
          (∑ q ∈ descendingUnpaidRigidCarriers B k,
            dyadicProfileSurplus k (projectedFree B) q.2))) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (cycles i) t) ≤ 2 ^ n := by
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
  change (∑ i : ProjectionOrdered V, 2 ^ k i) ≤ 2 ^ n
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
  have hterminal' :
      (softOverlapCompletionWords B).card +
        (netTransportableHardWords B k).card +
        (∑ q ∈ netRigidHardCarriers B k, 2 ^ k q.2) +
        (∑ q ∈ ascendingUnpaidRigidCarriers B k, 2 ^ k q.1) +
        (∑ q ∈ descendingUnpaidRigidCarriers B k, 2 ^ k q.2) +
        totalDyadicProfileLoss k (projectedFree B) ≤
      (2 ^ n - (coveredCompletionWords B).card) +
        (totalDyadicProfileSurplus k (projectedFree B) -
          (surplusPaidHardOverlapWords B k).card -
          (∑ q ∈ ascendingUnpaidRigidCarriers B k,
            dyadicProfileSurplus k (projectedFree B) q.1) -
          (∑ q ∈ descendingUnpaidRigidCarriers B k,
            dyadicProfileSurplus k (projectedFree B) q.2)) := by
    exact hterminal
  have hprior :=
    (completion_defect_payment_iff_after_terminal_hard_split
      B k hexp honeLoss).2 hterminal'
  exact planar_lower_branch_dyadic_capacity_of_both_mixed_rigid_net_payment
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles hprior

#print axioms planar_lower_branch_dyadic_capacity_of_terminal_hard_net_payment

end ProjectionOrdered
end JSP000404Research
