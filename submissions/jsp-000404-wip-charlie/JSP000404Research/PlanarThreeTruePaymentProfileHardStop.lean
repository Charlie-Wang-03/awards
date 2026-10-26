import JSP000404Research.PlanarTruePaymentCardinalityHardStop
import JSP000404Research.PlanarThreeSharpOverweightClassification
import Mathlib.Tactic

/-!
# Genuine original three-scale payment must eliminate EXACT residual profiles

This directly connects the kernel-checked n=3 seven/eight/nine
centre overweight classification to the ACTUAL source-native
eight-lane terminal payment hypothesis. In every forbidden
numerical original exponent profile, the exact genuine
external-hole / unreserved-dyadic-sources payment cannot hold.

It is a necessary condition on payment, not a counterexample:
no forbidden geometric AngleCap configuration is constructed here.
Nor does this imply the desired nonreusing allocation for the
remaining, numerically permitted profiles.
-/

namespace JSP000404Research
namespace ProjectionOrdered
open OrderedEdgeColoring
open DirectionData
open scoped BigOperators

/-- In n=3 the precise forbidden 7/8/9 original-centre exponent
profiles force the original exact payment inequality to FAIL for
every retained-active choice. All eight original debt classes are
still present in the inequality, not replaced with a proxy. -/
theorem original_three_forbidden_profile_forbids_actual_payment
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hseven : 7 ≤ Fintype.card V)
    (hbad :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let k : ProjectionOrdered V → ℕ :=
        fun i => centreExponent (cycles i) t
      (9 ≤ Fintype.card V ∨
        (Fintype.card V = 8 ∧
          (0 < ((Finset.univ : Finset (ProjectionOrdered V)).filter
            (fun i => k i = 1)).card ∨
           0 < ((Finset.univ : Finset (ProjectionOrdered V)).filter
            (fun i => k i = 2)).card)) ∨
        (Fintype.card V = 7 ∧
          (2 ≤ ((Finset.univ : Finset (ProjectionOrdered V)).filter
            (fun i => k i = 1)).card ∨
           1 ≤ ((Finset.univ : Finset (ProjectionOrdered V)).filter
            (fun i => k i = 2)).card)))) :
    ¬ (
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let htpos : 0 < t := by
        rw [ht]
        have hnr : (1 : ℝ) ≤ (3 : ℝ) := by norm_num
        linarith
      let hwidth : t < (3 : ℝ) + 1 := by rw [ht]; linarith
      let D := genericDirectionData_sendov hp hcap htpos hlam
      let B := standardResidualColoring D 3 (by exact_mod_cast hwidth)
      let k : ProjectionOrdered V → ℕ :=
        fun i => centreExponent (cycles i) t
      ∃ choice : ProjectionOrdered V → Fin 3,
        (∀ v ∈ projectedLossVertices B k,
          choice v ∈ retainedActive B v) ∧
        (terminalTwinOtherFiveDebt B k +
          ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
            (lossCoveredBlockerTripleWords B)).card +
          translatedLossDuplicateDebt B k choice ≤
          (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
            terminalTwinAvailableSurplus B k)) := by
  classical
  intro hpay
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hcard : Fintype.card (ProjectionOrdered V) = Fintype.card V :=
    projection_ordered_card_eq_original
  have hseven' : 7 ≤ Fintype.card (ProjectionOrdered V) := by omega
  have hdelta1 : delta < 1 := by linarith
  have hbad' :
      (9 ≤ Fintype.card (ProjectionOrdered V) ∨
        (Fintype.card (ProjectionOrdered V) = 8 ∧
          (0 < ((Finset.univ : Finset (ProjectionOrdered V)).filter
            (fun i => centreExponent (cycles i) t = 1)).card ∨
           0 < ((Finset.univ : Finset (ProjectionOrdered V)).filter
            (fun i => centreExponent (cycles i) t = 2)).card)) ∨
        (Fintype.card (ProjectionOrdered V) = 7 ∧
          (2 ≤ ((Finset.univ : Finset (ProjectionOrdered V)).filter
            (fun i => centreExponent (cycles i) t = 1)).card ∨
           1 ≤ ((Finset.univ : Finset (ProjectionOrdered V)).filter
            (fun i => centreExponent (cycles i) t = 2)).card))) := by
    dsimp only at hbad
    rcases hbad with hlarge | hcase8 | hcase7
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl ⟨by omega, hcase8.2⟩)
    · exact Or.inr (Or.inr ⟨by omega, hcase7.2⟩)
  have hover :
      8 < (∑ i : ProjectionOrdered V,
        (2 : ℕ) ^ centreExponent (cycles i) t) :=
    (planar_three_large_overweight_iff_obstruction_profile
      (reindexedPoint_injective hp)
      hdelta0 hdeltaHalf ht cycles hseven').mpr hbad'
  have hbound :
      (∑ i : ProjectionOrdered V,
        (2 : ℕ) ^ centreExponent (cycles i) t) ≤ 8 := by
    have hb :=
      planar_lower_branch_capacity_of_actual_retainedEdge_payment
        hp hcap (by decide : 1 ≤ (3 : ℕ))
        hdelta0 hdeltaHalf ht hlam cycles hpay
    simpa using hb
  omega

#print axioms original_three_forbidden_profile_forbids_actual_payment

end ProjectionOrdered
end JSP000404Research
