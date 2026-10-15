import JSP000404Research.ResidualTerminalTwinActiveExternalFrontier
import JSP000404Research.PlanarLowerBranchExternalHoleFrontier
import JSP000404Research.PlanarLowerBranchTerminalTwinNetReduction
import Mathlib.Tactic

/-!
# The sole planar lower-branch frontier with genuinely active flip choices

Proved without sorry: the original conditional lower-branch capacity follows
from existence of a retained-active flip assignment satisfying the external
true-hole payment obligation. This avoids the arbitrary constant-coordinate
choice in the earlier precise frontier.

Existence of active flip coordinates requires only the original exponent
bound and n≥1; the open ingredient is the GLOBAL payment inequality.
The theorem does NOT solve the geometric or combinatorial payment problem.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_lower_branch_capacity_of_exists_active_external_loss_payment
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
      ∃ choice : ProjectionOrdered V → Fin n,
        (∀ v ∈ projectedLossVertices B k,
          choice v ∈ retainedActive B v) ∧
        (terminalTwinOtherFiveDebt B k +
          (translatedLossCoveredWords B k choice).card +
          translatedLossDuplicateDebt B k choice ≤
          (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
            terminalTwinAvailableSurplus B k)) :
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
      ∃ choice : ProjectionOrdered V → Fin n,
        (∀ v ∈ projectedLossVertices B k,
          choice v ∈ retainedActive B v) ∧
        (terminalTwinOtherFiveDebt B k +
          (translatedLossCoveredWords B k choice).card +
          translatedLossDuplicateDebt B k choice ≤
          (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
            terminalTwinAvailableSurplus B k) := by
    exact hremaining
  have hraw :=
    (terminalTwinSixSourcePayment_iff_exists_active_externalFrontier
      B k hexp honeLoss hn).2 hnew
  let choice0 : ProjectionOrdered V → Fin n :=
    fun _ => ⟨0, by omega⟩
  have hfixed :
      terminalTwinOtherFiveDebt B k +
        (translatedLossCoveredWords B k choice0).card +
        translatedLossDuplicateDebt B k choice0 ≤
        (lossLedgerOutsideTranslatedTrueHoles B k choice0).card +
          terminalTwinAvailableSurplus B k := by
    exact (terminalTwinSixSourcePayment_iff_externalLossObstruction
      B k hexp honeLoss choice0).1 hraw
  exact planar_lower_branch_capacity_of_external_loss_obstruction
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles hfixed

#print axioms planar_lower_branch_capacity_of_exists_active_external_loss_payment

end ProjectionOrdered
end JSP000404Research
