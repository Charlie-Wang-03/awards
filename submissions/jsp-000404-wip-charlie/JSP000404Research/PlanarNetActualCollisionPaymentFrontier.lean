import JSP000404Research.PlanarStrictShellReserveLedger
import JSP000404Research.ResidualNetActualCollisionLedger
import Mathlib.Tactic

/-!
# Actual planar AngleCap: net-unpaid mobile-payment iff exact image payment

The previous admitted planar lower-branch frontier contains exactly
two mobile hard source masses: NET UNPAID forward-transportable and
reverse strictly descending rigid sources.

A verified global injection of these two finite families supplies
an exact reformulation of ANY remaining geometric payment goal:
after adding the unused singleton-or-soft sinks to its right side,
the two hard source masses on its left side may be replaced by
one shared singleton/soft sink capacity plus the GENUINE (not
hypothetical) NET cross-map collision set.

This genuine-planar theorem derives all one-layer prerequisites from
AngleCap and actual centre cycles. It produces the two budget PROOFS
as explicit existential witnesses and then certifies the reduction
uniformly in any other debt and any available payment budget.

The remaining payment inequality still has to be proved using real
Boolean holes and unreserved profile surplus. No new payment axiom
or JSP-000404 solution is asserted here.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_net_unpaid_mobile_payment_iff_actual_sink_credit
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
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
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
    ∃ (hexp : ∀ i : ProjectionOrdered V, k i ≤ n),
      ∃ (honeLoss : ∀ i : ProjectionOrdered V,
          (active B i).card ≤ n - k i + 1),
        ∀ (otherDebt availableBudget : ℕ),
          (otherDebt +
            (netTransportableHardWords B k).card +
            (netStrictDescentRigidWords B k).card ≤ availableBudget) ↔
          (otherDebt +
            (singletonCompletionWords B).card +
            (softOverlapCompletionWords B).card +
            (netActualForwardReverseCollisionWords
              B k hexp honeLoss).card ≤
            availableBudget +
              (netMobileUnusedCoveredSinkWords
                B k hexp honeLoss).card) := by
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
  change ∃ (hexp : ∀ i : ProjectionOrdered V, k i ≤ n),
    ∃ (honeLoss : ∀ i : ProjectionOrdered V,
        (active B i).card ≤ n - k i + 1),
      ∀ (otherDebt availableBudget : ℕ),
        (otherDebt +
          (netTransportableHardWords B k).card +
          (netStrictDescentRigidWords B k).card ≤ availableBudget) ↔
        (otherDebt +
          (singletonCompletionWords B).card +
          (softOverlapCompletionWords B).card +
          (netActualForwardReverseCollisionWords
            B k hexp honeLoss).card ≤
          availableBudget +
            (netMobileUnusedCoveredSinkWords
              B k hexp honeLoss).card)
  refine ⟨hexp, honeLoss, ?_⟩
  intro otherDebt availableBudget
  exact net_mobile_payment_iff_actual_collision_unused_sink_credit
    B k hexp honeLoss otherDebt availableBudget

#print axioms planar_net_unpaid_mobile_payment_iff_actual_sink_credit

end ProjectionOrdered
end JSP000404Research
