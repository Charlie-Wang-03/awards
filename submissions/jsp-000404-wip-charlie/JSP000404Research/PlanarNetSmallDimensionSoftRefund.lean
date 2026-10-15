import JSP000404Research.PlanarNetLowColourNoDuplicate
import JSP000404Research.ResidualNetCollisionSmallDimensionSoftRefund
import Mathlib.Tactic

/-!
# Actual AngleCap NET first-hit SOFT refund in dimensions one and two

This applies the new abstract certified NET SOFT first-hit refund
to the GENUINE planar standard residual colouring with actual centre
exponents. Neither the local palette bound nor the exponent bound
is added as an external assumption: both are obtained from the
existing planar AngleCap centre-cycle construction.

For n<=2 the total certified first-hit plus duplicate incidence
debt is bounded by the number of distinct ACTUAL soft overlap words.

This is not the full six-source true-hole/unreserved-surplus payment.
Covered SOFT words must not be treated as true holes.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_net_low_colour_actual_soft_first_hits_le
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hnTwo : n ≤ 2)
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
    let hwidth : t < (n : ℝ) + 1 := by
      rw [ht]
      linarith
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D n (by exact_mod_cast hwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    ∃ (hexp : ∀ i : ProjectionOrdered V, k i ≤ n),
      ∃ (honeLoss : ∀ i : ProjectionOrdered V,
        (active B i).card ≤ n - k i + 1),
        netCollisionCertifiedDuplicateDebt B k hexp honeLoss +
          (netCollisionCertifiedDiagonalWords B k hexp honeLoss).card ≤
            (softOverlapCompletionWords B).card := by
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
  change ∃ (hexp : ∀ i : ProjectionOrdered V, k i ≤ n),
      ∃ (honeLoss : ∀ i : ProjectionOrdered V,
        (active B i).card ≤ n - k i + 1),
        netCollisionCertifiedDuplicateDebt B k hexp honeLoss +
          (netCollisionCertifiedDiagonalWords B k hexp honeLoss).card ≤
            (softOverlapCompletionWords B).card
  obtain ⟨hexp, honeLoss, _, _⟩ :=
    planar_net_low_colour_no_duplicate_and_mobile_payment
      hp hcap hn hnTwo hdelta0 hdeltaHalf ht hlam cycles
  exact ⟨hexp, honeLoss,
    net_first_hits_plus_duplicates_le_actual_soft_of_n_le_two
      B k hexp honeLoss hnTwo⟩

#print axioms planar_net_low_colour_actual_soft_first_hits_le

end ProjectionOrdered
end JSP000404Research
