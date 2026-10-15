import JSP000404Research.ResidualTerminalTwinExternalHoleFrontier
import JSP000404Research.PlanarLowerBranchTerminalTwinNetReduction
import Mathlib.Tactic

/-!
# The admitted planar lower branch, reduced to external true holes

This theorem is fully conditional and sorry-free. It changes neither
the Sendov input nor the six debt classes: it replaces the old global
six-source payment hypothesis by its kernel-equivalent outstanding
external-true-hole condition.

The remaining geometric proof has NOT been supplied, and this theorem
does not imply the original lower-branch conjecture unconditionally.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_lower_branch_capacity_of_external_loss_obstruction
    {V : Type*} [Fintype V]
    {p : V → Plane}
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
    (hremaining :
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
      let choice : ProjectionOrdered V → Fin n :=
        fun _ => ⟨0, by omega⟩
      terminalTwinOtherFiveDebt B k +
        (translatedLossCoveredWords B k choice).card +
        translatedLossDuplicateDebt B k choice ≤
        (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
          terminalTwinAvailableSurplus B k) :
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
  let choice : ProjectionOrdered V → Fin n :=
    fun _ => ⟨0, by omega⟩
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
  have hnew :
      terminalTwinOtherFiveDebt B k +
        (translatedLossCoveredWords B k choice).card +
        translatedLossDuplicateDebt B k choice ≤
        (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
          terminalTwinAvailableSurplus B k := by
    exact hremaining
  have hold :=
    (terminalTwinSixSourcePayment_iff_externalLossObstruction
      B k hexp honeLoss choice).2 hnew
  have hterminal :
      (softOverlapCompletionWords B).card +
        (netTransportableHardWords B k).card +
        (netStrictDescentRigidWords B k).card +
        (∑ q ∈ netTwinRigidCarriers B k, 2 ^ k q.2) +
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
    simpa only [terminalTwinOtherFiveDebt,
      terminalTwinAvailableSurplus] using hold
  exact planar_lower_branch_dyadic_capacity_of_terminal_twin_net_payment
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles hterminal

#print axioms planar_lower_branch_capacity_of_external_loss_obstruction

end ProjectionOrdered
end JSP000404Research
