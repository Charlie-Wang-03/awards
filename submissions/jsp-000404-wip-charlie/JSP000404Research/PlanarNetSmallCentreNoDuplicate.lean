import JSP000404Research.ResidualNetCollisionEightCentreBarrier
import JSP000404Research.PlanarNetLowColourNoDuplicate
import JSP000404Research.PlanarLowerBranchTerminalTwinNetReduction
import JSP000404Research.PlanarStandardResidualBudget
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Genuine planar AngleCap small-centre NET duplicate-debt closure

The one-layer residual budget is not an external assumption in a
valid lower-branch AngleCap configuration; it follows from the actual
projective centre cycles and the standard residual colouring.

Here we instantiate the already proved EIGHT-CENTRE BARRIER
with the genuine planar residual colouring and the actual
centre-exponent profile. For ANY n>=1 but at most SEVEN
original plane centres, the canonical NET diagonal map has
zero duplicate debt.
The corresponding mobile hard ledger therefore has no additional
multiple-target-hit term.

Covered diagonals (including hard source and fifth-centre blockers),
soft overlap mass, rigid twins, mixed rigid, and projected profile
loss remain explicit: the total dyadic capacity theorem and its one
remaining global geometric payment sorry are NOT established.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- ACTUAL AngleCap configurations with |V|<=7 admit their
standard one-layer residual colouring with the certified
global NET duplication debt equal to ZERO. Moreover, the
mobile hard source mass is bounded by singleton, soft, TRUE
Boolean holes and DISTINCT covered opposite diagonals with
NO extra multiple-hit term.

The existential evidence ensures this is a real planar theorem,
not an arbitrarily supplied abstract one-layer hypothesis. -/
theorem planar_net_small_centre_no_duplicate_and_mobile_payment
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hcentres : Fintype.card V ≤ 7)
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
        netCollisionCertifiedDuplicateDebt B k hexp honeLoss = 0 ∧
        (netTransportableHardWords B k).card +
          (netStrictDescentRigidWords B k).card ≤
          (singletonCompletionWords B).card +
          (softOverlapCompletionWords B).card +
          ((Finset.univ : Finset (Fin n → Bool)) \
            coveredCompletionWords B).card +
          (netCollisionCertifiedCoveredDiagonals
            B k hexp honeLoss).card := by
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
  change ∃ (hexp : ∀ i : ProjectionOrdered V, k i ≤ n),
      ∃ (honeLoss : ∀ i : ProjectionOrdered V,
        (active B i).card ≤ n - k i + 1),
        netCollisionCertifiedDuplicateDebt B k hexp honeLoss = 0 ∧
        (netTransportableHardWords B k).card +
          (netStrictDescentRigidWords B k).card ≤
          (singletonCompletionWords B).card +
          (softOverlapCompletionWords B).card +
          ((Finset.univ : Finset (Fin n → Bool)) \
            coveredCompletionWords B).card +
          (netCollisionCertifiedCoveredDiagonals
            B k hexp honeLoss).card
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
  have hsize : Fintype.card (ProjectionOrdered V) ≤ 7 := by
    have hcardeq :
        Fintype.card (ProjectionOrdered V) = Fintype.card V := by
      let e : ProjectionOrdered V ≃ V :=
        { toFun := ProjectionOrdered.toOriginal
          invFun := ProjectionOrdered.ofOriginal
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact Fintype.card_congr e
    omega
  refine ⟨hexp, honeLoss, ?_, ?_⟩
  · exact net_collision_duplicate_debt_zero_of_at_most_seven_centres
      B k hexp honeLoss hsize
  · exact net_mobile_mass_le_without_duplicates_of_at_most_seven_centres
      B k hexp honeLoss hsize

#print axioms planar_net_small_centre_no_duplicate_and_mobile_payment

end ProjectionOrdered
end JSP000404Research
