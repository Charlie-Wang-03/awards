import JSP000404Research.PlanarLowerBranchActualEdgeCarrierFrontier
import Mathlib.Tactic

/-!
# Original-plane overcrowding is a direct obstruction to ACTUAL eight-source payment

The existing verified conditional implication
  source-native external-hole / unreserved-surplus payment -> dyadic capacity
has a sharp structural consequence. Every original centre contributes at
least one natural dyadic unit. Therefore any actual AngleCap configuration
with more than 2^n original centres cannot admit the claimed genuine
global external-hole payment, regardless of how its retained-active
loss coordinates are selected.

This is a *necessary* anti-certificate of the currently missing
source-native payment theorem, NOT a disproof of Blumenthal's problem:
it does NOT establish that an overcrowded AngleCap configuration exists.

No external hole is manufactured, and no additional sorry/axiom is used.
-/

namespace JSP000404Research
namespace ProjectionOrdered
open OrderedEdgeColoring
open DirectionData
open scoped BigOperators

/-- Every original point accounts for at least one unit of genuine
dyadic mass. This does not rely on artificial Boolean encodings. -/
theorem original_centre_card_le_dyadic_mass
    {V : Type*} [Fintype V]
    (k : V → ℕ) :
    Fintype.card V ≤ (∑ i : V, (2 : ℕ) ^ k i) := by
  classical
  have hpoint : ∀ i : V, 1 ≤ (2 : ℕ) ^ k i := by
    intro i
    have hh : 0 < (2 : ℕ) ^ k i := by positivity
    omega
  calc
    Fintype.card V = (∑ _i : V, (1 : ℕ)) := by simp
    _ ≤ (∑ i : V, (2 : ℕ) ^ k i) := by
      apply Finset.sum_le_sum
      intro i _
      exact hpoint i

/-- The genuine original projection-order construction retains the
number of input geometric centres without adding or removing any. -/
theorem projection_ordered_card_eq_original
    {V : Type*} [Fintype V] :
    Fintype.card (ProjectionOrdered V) = Fintype.card V := by
  let e : ProjectionOrdered V ≃ V :=
    { toFun := ProjectionOrdered.toOriginal
      invFun := ProjectionOrdered.ofOriginal
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.card_congr e

/-- DIRECT GLOBAL PAYMENT HARD STOP. Under original AngleCap data, a
strictly overcrowded configuration (>2^n ORIGINAL centres) prevents
the exact outstanding actual-retained-edge payment condition for
EVERY choice, including every original retained-active choice.

This does NOT assert that an overcrowded plane AngleCap configuration
exists; if geometry excludes it, this conditional obstruction is
vacuous. Conversely, any future proof that universal payment follows
from AngleCap MUST in particular rule out original overcrowding. -/
theorem original_overcrowding_forbids_actual_external_payment
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
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hovercrowded : 2 ^ n < Fintype.card V) :
    ¬ (
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
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
          translatedLossDuplicateDebt B k choice ≤
          (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
            terminalTwinAvailableSurplus B k)) := by
  classical
  intro hpayment
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hbound :
      (∑ i : ProjectionOrdered V,
        (2 : ℕ) ^ centreExponent (cycles i) t) ≤ 2 ^ n :=
    planar_lower_branch_capacity_of_actual_retainedEdge_payment
      hp hcap hn hdelta0 hdeltaHalf ht hlam cycles hpayment
  have hlow :
      Fintype.card (ProjectionOrdered V) ≤
        (∑ i : ProjectionOrdered V,
          (2 : ℕ) ^ centreExponent (cycles i) t) :=
    original_centre_card_le_dyadic_mass
      (fun i : ProjectionOrdered V => centreExponent (cycles i) t)
  have hcard : Fintype.card (ProjectionOrdered V) = Fintype.card V :=
    projection_ordered_card_eq_original
  omega

#print axioms original_centre_card_le_dyadic_mass
#print axioms projection_ordered_card_eq_original
#print axioms original_overcrowding_forbids_actual_external_payment

end ProjectionOrdered
end JSP000404Research
