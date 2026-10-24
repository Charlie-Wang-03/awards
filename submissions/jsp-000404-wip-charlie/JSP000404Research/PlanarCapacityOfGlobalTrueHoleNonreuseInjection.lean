import JSP000404Research.ActualExternalHoleNonreuseCertificate
import JSP000404Research.PlanarLowerBranchActualEdgeCarrierFrontier
import Mathlib.Tactic

/-!
# Genuine all-cardinality planar capacity from ONE nonreusing allocation

A geometric matching from three SOURCE-TAGGED classes of actual debt to
actual outside-translated Boolean holes or genuinely unreserved surplus is
sufficient for the original all-cardinality capacity theorem.

This fully kernel-checked reduction DOES NOT establish that such a matching
always exists. Producing it under AngleCap is precisely the outstanding
mathematical obligation at the main admitted proof root.
-/

namespace JSP000404Research
namespace ProjectionOrdered
open OrderedEdgeColoring

theorem planar_lower_branch_capacity_of_global_true_hole_nonreuse_injection
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
    (hallocation :
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
        ∃ f : actualExternalPaymentDebts B k choice →
            actualExternalPaymentCredits B k choice,
          Function.Injective f) :
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
  let B := standardResidualColoring D n (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  have hpayout :
      ∃ choice : ProjectionOrdered V → Fin n,
        (∀ v ∈ projectedLossVertices B k,
          choice v ∈ retainedActive B v) ∧
        (terminalTwinOtherFiveDebt B k +
          ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
            (lossCoveredBlockerTripleWords B)).card +
          translatedLossDuplicateDebt B k choice ≤
          (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
            terminalTwinAvailableSurplus B k) := by
    obtain ⟨choice, hactive, f, hf⟩ := hallocation
    refine ⟨choice, hactive, ?_⟩
    exact actual_external_hole_nonreuse_certificate_implies_payment
      B k choice f hf
  exact planar_lower_branch_capacity_of_actual_retainedEdge_payment
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles hpayout

#print axioms planar_lower_branch_capacity_of_global_true_hole_nonreuse_injection
end ProjectionOrdered
end JSP000404Research
