import JSP000404Research.PlanarNetSmallCentreNoDuplicate
import JSP000404Research.ResidualNetCollisionNineCentreRigidExhaustion
import JSP000404Research.PlanarLowerBranchTerminalTwinNetReduction
import JSP000404Research.PlanarStandardResidualBudget
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# ACTUAL planar AngleCap <=9-centre NET duplicate / terminal twin tradeoff

For the true Sendov/AngleCap residual colouring obtained from
projection ordering, genuine direction data, and centre projective
cycles, construct the non-assumed ONE-LAYER budget witnesses.

If there are at most NINE original plane centres, either
  (1) genuine canonical NET duplicate-image debt is ZERO, or
  (2) equal-exponent terminal TWIN rigid carrier debt is ZERO.

In particular, the sum of the two competing natural-valued
liabilities equals their MAXIMUM, as certified by Lean.

This is a nontrivial geometric application of SOURCE-native
four-hard-carrier exhaustion, but it is CONDITIONAL on <=9
original centres. The full six-class unrestricted AngleCap
dyadic capacity inequality retains its one admitted sorry.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- Real planar projective AngleCap configurations with at most
NINE original centres have competing NET duplicate and terminal
TWIN rigid dyadic masses that cannot both be positive. All
one-layer source/exponent requirements are DERIVED geometrically
rather than supplied by a separate abstract hypothesis. -/
theorem planar_net_nine_centres_duplicate_twin_mass_exclusive
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hcentres : Fintype.card V ≤ 9)
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
        (netCollisionCertifiedDuplicateDebt B k hexp honeLoss = 0 ∨
          netTwinRigidCarriers B k = ∅) ∧
        netCollisionCertifiedDuplicateDebt B k hexp honeLoss +
          (∑ r ∈ netTwinRigidCarriers B k, (2 : ℕ) ^ k r.2) =
          max (netCollisionCertifiedDuplicateDebt B k hexp honeLoss)
            (∑ r ∈ netTwinRigidCarriers B k,
              (2 : ℕ) ^ k r.2) := by
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
        (netCollisionCertifiedDuplicateDebt B k hexp honeLoss = 0 ∨
          netTwinRigidCarriers B k = ∅) ∧
        netCollisionCertifiedDuplicateDebt B k hexp honeLoss +
          (∑ r ∈ netTwinRigidCarriers B k, (2 : ℕ) ^ k r.2) =
          max (netCollisionCertifiedDuplicateDebt B k hexp honeLoss)
            (∑ r ∈ netTwinRigidCarriers B k,
              (2 : ℕ) ^ k r.2)
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
  have hsize : Fintype.card (ProjectionOrdered V) ≤ 9 := by
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
  · exact net_collision_nine_centres_duplicate_or_twin_zero
      B k hexp honeLoss hsize
  · exact net_collision_nine_centres_duplicate_plus_twin_mass_eq_max
      B k hexp honeLoss hsize

#print axioms planar_net_nine_centres_duplicate_twin_mass_exclusive

end ProjectionOrdered
end JSP000404Research
