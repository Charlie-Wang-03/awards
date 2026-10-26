import JSP000404Research.PlanarLowerBranchExactCoveredTranslatedFrontier
import Mathlib.Tactic

/-!
# Any ORIGINAL planar overweight counterexample must exhibit exact shortfall

Unlike assuming enough resources and then deriving capacity, this theorem
STARTS FROM AN ORIGINAL ANGLECAP planar configuration whose exact dyadic
weight is strictly OVER 2^n, and concludes that EVERY actually active
choice of loss-flip coordinates must have a STRICT deficiency of
nonlocal real-hole/unreserved-sink credits relative to all ORIGINAL
other debts plus the exactly partitioned eighth-source obstructions.

The covered candidate class and uncovered-translated-loss class are
DISJOINT by the imported certified exact ledger. There are no extra
synthetic credit tokens and no source omission. This is a REAL,
kernel-checkable necessary shape of a would-be counterexample, NOT an
exclusion of these configurations or a solution of the remaining
geometric AngleCap-to-payment gap.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- Every originally overweight planar configuration forces, for
EACH genuinely active flip-coordinate choice, the strict failure of
the exact nonlocal budget: uncovered/translated-captured and covered
original eighth-source candidates are counted DISJOINTLY. This is
the logically strongest direct contrapositive of the exact planar
conditional payment bridge, and it does not assume geometric payout. -/
theorem planar_overweight_forces_exact_two_class_nonlocal_shortfall
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
    (hover :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      2 ^ n < (∑ i : ProjectionOrdered V,
        2 ^ centreExponent (cycles i) t)) :
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
    ∀ choice : ProjectionOrdered V → Fin n,
      (∀ v ∈ projectedLossVertices B k,
        choice v ∈ retainedActive B v) →
      ((lossLedgerOutsideTranslatedTrueHoles B k choice) \
        actualLossEarliestOppositeCandidateWords B k choice).card +
        terminalTwinAvailableSurplus B k <
      terminalTwinOtherFiveDebt B k +
        ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)).card +
        ((translatedLossDuplicateDebt B k choice -
            (actualLossEarliestOppositeCandidateWords B k choice).card) +
          ((actualEarliestCoveredOppositeDefect B k choice).card +
            (actualEarliestUncoveredTranslatedOppositeDefect B k choice).card)) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by
    rw [ht]
    have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwidth : t < (n : ℝ) + 1 := by rw [ht]; linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  intro choice hactive
  by_contra hnot
  have hbudget :
      terminalTwinOtherFiveDebt B k +
          ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
            (lossCoveredBlockerTripleWords B)).card +
          ((translatedLossDuplicateDebt B k choice -
              (actualLossEarliestOppositeCandidateWords B k choice).card) +
            ((actualEarliestCoveredOppositeDefect B k choice).card +
              (actualEarliestUncoveredTranslatedOppositeDefect B k choice).card)) ≤
        ((lossLedgerOutsideTranslatedTrueHoles B k choice) \
          actualLossEarliestOppositeCandidateWords B k choice).card +
          terminalTwinAvailableSurplus B k := by omega
  have hpayment :
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
            terminalTwinAvailableSurplus B k) :=
    ⟨choice, hactive, hbudget⟩
  have hcapBound :
      (∑ i : ProjectionOrdered V,
        2 ^ centreExponent (cycles i) t) ≤ 2 ^ n :=
    planar_lower_branch_capacity_of_exact_covered_translated_nonlocal_payment
      hp hcap hn hdelta0 hdeltaHalf ht hlam cycles hpayment
  exact (not_le_of_gt hover) hcapBound

#print axioms planar_overweight_forces_exact_two_class_nonlocal_shortfall

end ProjectionOrdered
end JSP000404Research
