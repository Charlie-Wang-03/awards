import JSP000404Research.ActualEightSourceEarliestHallBridge
import JSP000404Research.PlanarCapacityOfEightSourceNonreuseMatching
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Tactic

/-!
# Source-native eight-class finite Hall frontier for the ORIGINAL plane

This module connects the existing, kernel-proved ACTUAL earliest-prior
source debt records (as opposed to anonymous Fin-valued duplicate-debt
tokens) directly to the ORIGINAL planar dyadic capacity result.

For each genuine original AngleCap instance, if some retained-active
choice and some geometrically justified eligibility relation satisfy
Hall expansion against exactly the already-unreserved surplus and
GLOBAL true holes, then all eight original debt lanes are paid by one
nonreusing injection and the target capacity follows.

The complementary finite Hall dichotomy gives an explicit, finite
deficient source family whenever such a selected eligibility relation
cannot support a nonreusing allocation. This is a testable NO-GO
certificate for that payment scheme, not a disproof of JSP-000404.

NO universal planar Hall expansion has been established. The ROOT
global sorry remains open and is not replaced by a conditional claim.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- For each concrete source-native eight-lane debt instance and an
explicit eligibility relation into the TWO ACTUAL legal credit
classes: either there is a single injective allocation respecting
all eligibility sets, or a finite source family has strictly
fewer distinct eligible real credit tokens than actual sources.

This is finite Hall duality; it does NOT assert either alternative
unconditionally holds in any particular geometric configuration. -/
theorem actual_earliest_eight_source_hall_allocation_or_deficit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n)
    (eligible :
      actualEightSourceEarliestDebtTokens B k choice →
        Finset (actualExternalPaymentCredits B k choice)) :
    (∃ allocate :
      actualEightSourceEarliestDebtTokens B k choice →
        actualExternalPaymentCredits B k choice,
        Function.Injective allocate ∧
          ∀ s, allocate s ∈ eligible s) ∨
    (∃ S : Finset (actualEightSourceEarliestDebtTokens B k choice),
      (S.biUnion eligible).card < S.card) := by
  classical
  by_cases hHall :
      ∀ S : Finset (actualEightSourceEarliestDebtTokens B k choice),
        S.card ≤ (S.biUnion eligible).card
  · left
    obtain ⟨allocate, hinj, hreal⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective eligible).mp hHall
    exact ⟨allocate, hinj, hreal⟩
  · right
    push_neg at hHall
    exact hHall

#print axioms actual_earliest_eight_source_hall_allocation_or_deficit

end OrderedEdgeColoring

namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- END-TO-END source-native Hall-to-original-capacity implication.

The new step is the rigorous composition of the ACTUAL, typed
earliest-prior collision tokens in the eighth debt lane with the
complete ORIGINAL geometric planar claim.

The HALL expansion is an EXPLICIT UNPROVED geometric hypothesis
and not silently derived from AngleCap. The source type, all eight
debt classes and the genuine outside-translated TRUE holes and
genuinely unreserved dyadic profile surplus are unchanged. -/
theorem planar_lower_branch_capacity_of_actual_earliest_eight_source_hall
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
    (hGeometricHall :
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
        ∃ eligible :
          actualEightSourceEarliestDebtTokens B k choice →
            Finset (actualExternalPaymentCredits B k choice),
          ∀ S : Finset (actualEightSourceEarliestDebtTokens B k choice),
            S.card ≤ (S.biUnion eligible).card) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (cycles i) t) ≤ 2 ^ n := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by
    rw [ht]
    have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwidth : t < (n : ℝ) + 1 := by rw [ht]; linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B := standardResidualColoring D n (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  obtain ⟨choice, hactive, eligible, hHall⟩ := hGeometricHall
  have hpay :=
    actual_eight_source_earliest_hall_implies_global_payment
      B k choice eligible hHall
  exact planar_lower_branch_capacity_of_actual_retainedEdge_payment
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
    ⟨choice, hactive, hpay⟩

#print axioms planar_lower_branch_capacity_of_actual_earliest_eight_source_hall

end ProjectionOrdered
end JSP000404Research
