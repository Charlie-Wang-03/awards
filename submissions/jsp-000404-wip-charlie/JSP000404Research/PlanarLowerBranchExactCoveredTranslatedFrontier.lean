import JSP000404Research.PlanarLowerBranchActualEdgeCarrierFrontier
import JSP000404Research.ActualEarliestExactCoveredVsTranslatedDefect
import Mathlib.Tactic

/-!
# Planar original lower branch from the TWO DISJOINT exact nonlocal collision defects

This is a formal AngleCap-geometry-facing endpoint for the strongest exact
source-native collision ledger: the ORIGINAL eight-source payment inequality
has an equivalent residual form after cancelling only GENUINE local
outside-translated Boolean holes, and partitioning all ineligible opposite
candidates into concrete COVERED versus UNCOVERED-TRANSLATED word classes.

The remaining geometric obligation is NOT zero: the other seven source-tagged
debt classes, repeated opposite-target collisions, plus covered candidates and
uncovered-but-translated-loss-captured candidates must jointly fit into real nonlocal true holes + genuinely
unreserved surplus. These resources are the original credit supply with
eligible local collision holes removed by the EXACT numeric identity.

This theorem does not assume or prove a global assignment from AngleCap. It
is a sorry-free SUFFICIENCY bridge into the root capacity statement; the
matching/existence step under AngleCap remains the sole open root branch.
The root proof already closes n=1,2 and centres<=4, so the new obligation
is useful in the genuinely open n>=3, centres>=5 regime.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- Formal exact residual front-end of the already certified planar
lower-branch theorem: one *source-native* actual active flip choice with
a NONLOCAL surplus/true-hole budget suffices to prove dyadic capacity.
This does NOT derive the residual inequality from AngleCap. -/
theorem planar_lower_branch_capacity_of_exact_covered_translated_nonlocal_payment
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
    (hnonlocal :
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
          ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
            (lossCoveredBlockerTripleWords B)).card +
          ((translatedLossDuplicateDebt B k choice -
              (actualLossEarliestOppositeCandidateWords B k choice).card) +
            ((actualEarliestCoveredOppositeDefect B k choice).card +
              (actualEarliestUncoveredTranslatedOppositeDefect B k choice).card)) ≤
          ((lossLedgerOutsideTranslatedTrueHoles B k choice) \
            actualLossEarliestOppositeCandidateWords B k choice).card +
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
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  have horiginal :
      ∃ choice : ProjectionOrdered V → Fin n,
        (∀ v ∈ projectedLossVertices B k,
          choice v ∈ retainedActive B v) ∧
        (terminalTwinOtherFiveDebt B k +
          ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
            (lossCoveredBlockerTripleWords B)).card +
          translatedLossDuplicateDebt B k choice ≤
          (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
            terminalTwinAvailableSurplus B k) := by
    obtain ⟨choice, hactive, hbudget⟩ := hnonlocal
    refine ⟨choice, hactive, ?_⟩
    exact (actual_eight_source_payment_iff_exact_two_nonlocal_defect_classes
      B k choice).2 hbudget
  exact planar_lower_branch_capacity_of_actual_retainedEdge_payment
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles horiginal

#print axioms planar_lower_branch_capacity_of_nonlocal_collision_defect_payment

end ProjectionOrdered
end JSP000404Research
