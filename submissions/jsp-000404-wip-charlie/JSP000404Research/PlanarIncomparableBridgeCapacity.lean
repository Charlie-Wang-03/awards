import JSP000404Research.PlanarNetActualCollisionPaymentFrontier
import JSP000404Research.ResidualIncomparableBridgePool
import Mathlib.Tactic

/-!
# Actual planar AngleCap: NET mobile hard mass with incomparable-only bridge debt

In the real standard-residual geometry, under precisely the existing
AngleCap and true centre-projective-cycle assumptions, derive the
one-layer bound and apply the strengthened abstract collision theorem:

  net forward hard + reverse strict hard + UNUSED covered sink credit
    <= singleton covered + soft covered
       + SUM_(only palette-INCOMPARABLE bridge soft carriers)
           2^commonInactiveCard.

This strictly filters the possible collision carrier family compared
with the earlier sum over ALL candidate bridges. The word "strictly"
here describes the filtering criterion, not an assertion that the
filtered set is a proper subset in every planar configuration.

No new geometric axiom is assumed. All right-side sinks are COVERED
and the inequality does not prove the missing true-hole/surplus
payment needed for the entire JSP-000404 lower branch.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_net_mobile_mass_plus_unused_le_incomparable_bridge_dyadic
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
        (netTransportableHardWords B k).card +
          (netStrictDescentRigidWords B k).card +
            (netMobileUnusedCoveredSinkWords
              B k hexp honeLoss).card ≤
          (singletonCompletionWords B).card +
            (softOverlapCompletionWords B).card +
            (∑ r ∈ incomparableBridgeSoftCarriers B k,
              2 ^ (commonRetainedInactive B r.1 r.2).card) := by
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
      (netTransportableHardWords B k).card +
        (netStrictDescentRigidWords B k).card +
          (netMobileUnusedCoveredSinkWords
            B k hexp honeLoss).card ≤
        (singletonCompletionWords B).card +
          (softOverlapCompletionWords B).card +
          (∑ r ∈ incomparableBridgeSoftCarriers B k,
            2 ^ (commonRetainedInactive B r.1 r.2).card)
  exact ⟨hexp, honeLoss,
    net_mobile_mass_plus_unused_sink_le_incomparable_bridge_dyadic
      B k hexp honeLoss⟩

#print axioms planar_net_mobile_mass_plus_unused_le_incomparable_bridge_dyadic

end ProjectionOrdered
end JSP000404Research
