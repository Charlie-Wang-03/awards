import JSP000404Research.PlanarOverweightNecessaryTwoDefectShortfall
import Mathlib.Tactic

/-!
# NONVACUOUS canonical active-choice obstruction for hypothetical counterexamples

The main strict-shortfall theorem applies to EVERY active loss-flip
choice, but one could worry that no active choice exists. In original
AngleCap geometry and under the precise one-layer exponent bound,
there is ALWAYS a genuinely retained-active choice at each loss owner.

We construct that canonical choice explicitly using the EXISTING
projectedLossActiveFlipChoice lemma and apply the strict-shortfall
theorem. Therefore any planar overweight counterexample would give
a real, concrete original-source nonlocal deficit witness, not merely
a vacuous implication about choices that fail to exist.

We do NOT rule out this necessary witness geometrically here.
-/

namespace JSP000404Research
namespace ProjectionOrdered
open OrderedEdgeColoring
open DirectionData

/-- Every true original planar overweight counterexample produces an
ACTUAL retained-active canonical choice, and that choice witnesses
STRICT deficiency of genuine external-hole/unused-surplus credits
against exact original nonlocal debt. -/
theorem planar_overweight_has_canonical_active_two_class_shortfall
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
    ∃ choice : ProjectionOrdered V → Fin n,
      (∀ v ∈ projectedLossVertices B k,
        choice v ∈ retainedActive B v) ∧
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
  have hdelta1 : delta < 1 := by linarith
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
  have hexp : ∀ v : ProjectionOrdered V, k v ≤ n := by
    intro v
    exact Nat.le_of_lt
      (centreExponent_lt_n (cycles v) n delta t
        hn hdelta0 hdelta1 ht)
  let choice : ProjectionOrdered V → Fin n :=
    projectedLossActiveFlipChoice B k hexp hn
  have hactive : ∀ v ∈ projectedLossVertices B k,
      choice v ∈ retainedActive B v := by
    intro v hv
    exact projectedLossActiveFlipChoice_mem_retainedActive
      B k hexp hn hv
  have hstrict :=
    planar_overweight_forces_exact_two_class_nonlocal_shortfall
      hp hcap hn hdelta0 hdeltaHalf ht hlam cycles hover choice hactive
  change ∃ choice : ProjectionOrdered V → Fin n,
      (∀ v ∈ projectedLossVertices B k,
        choice v ∈ retainedActive B v) ∧
      ((lossLedgerOutsideTranslatedTrueHoles B k choice) \
        actualLossEarliestOppositeCandidateWords B k choice).card +
        terminalTwinAvailableSurplus B k <
      terminalTwinOtherFiveDebt B k +
        ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)).card +
        ((translatedLossDuplicateDebt B k choice -
            (actualLossEarliestOppositeCandidateWords B k choice).card) +
          ((actualEarliestCoveredOppositeDefect B k choice).card +
            (actualEarliestUncoveredTranslatedOppositeDefect B k choice).card))
  exact ⟨choice, hactive, hstrict⟩

#print axioms planar_overweight_has_canonical_active_two_class_shortfall

end ProjectionOrdered
end JSP000404Research
