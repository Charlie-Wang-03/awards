import JSP000404Research.PlanarNetActualCollisionPaymentFrontier
import JSP000404Research.ResidualIncomparableBridgeCodimension
import Mathlib.Tactic

/-!
# Genuine planar AngleCap: numerical quarter-dimensional collision bound

For the actual planar standard residual colouring and canonical
centre-projective-cycle exponents, the two NET UNPAID hard source masses
plus the exactly unused eligible covered sink credit fit inside
singleton/soft covered sinks and at most 2^(n-2) additional units PER
candidate oriented soft bridge with incomparable active palettes.

Every collision bridge needs TWO independent active colour witnesses:
a forward-flip coordinate in reverse-lower but not forward-upper,
and a reverse-flip coordinate in forward-upper but not reverse-lower.
Therefore no bridge face can have more than n-2 free coordinates.

This planar specialization is unconditional BEYOND the existing AngleCap
and real centre-cycle hypotheses. It is a collision-count/density
bound, NOT a true-hole or unreserved-surplus payment, and cannot close
JSP-000404 by itself.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_net_mobile_mass_plus_unused_le_incomparable_bridge_density
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
            (incomparableBridgeSoftCarriers B k).card * 2 ^ (n - 2) := by
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
          (incomparableBridgeSoftCarriers B k).card * 2 ^ (n - 2)
  exact ⟨hexp, honeLoss,
    net_mobile_source_plus_unused_le_covered_plus_quarter_density
      B k hexp honeLoss⟩

#print axioms planar_net_mobile_mass_plus_unused_le_incomparable_bridge_density

end ProjectionOrdered
end JSP000404Research
