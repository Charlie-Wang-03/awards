import JSP000404Research.PlanarNetNineCentreTwinTradeoff
import JSP000404Research.ResidualNetCollisionElevenCentreTwinMass
import Mathlib.Tactic

/-!
# Actual planar AngleCap NET/TWIN dyadic mass limit (<=11 centres)

Under true planar projection-cycle and AngleCap assumptions, if there
is at most eleven original centres and actual NET duplicate debt is
positive, the surviving equal-exponent TWIN rigid dyadic mass is <=
2^(n-1). This uses the strict k<n geometric exponent bound.

This caps a liability; it does NOT identify an unreserved dyadic payment
source or prove the unrestricted six-source inequality.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_net_eleven_centres_duplicate_or_twin_mass_le
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hcentres : Fintype.card V ≤ 11)
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
        netCollisionCertifiedDuplicateDebt B k hexp honeLoss = 0 ∨
          (∑ p ∈ netTwinRigidCarriers B k, (2 : ℕ) ^ k p.2) ≤ (2 : ℕ) ^ (n - 1) := by
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
        netCollisionCertifiedDuplicateDebt B k hexp honeLoss = 0 ∨
          (∑ p ∈ netTwinRigidCarriers B k, (2 : ℕ) ^ k p.2) ≤ (2 : ℕ) ^ (n - 1)
  have hstrict : ∀ i : ProjectionOrdered V, k i < n := by
    intro i
    exact centreExponent_lt_n (cycles i) n delta t
      hn hdelta0 hdelta1 ht
  have hexp : ∀ i : ProjectionOrdered V, k i ≤ n :=
    fun i => (hstrict i).le
  have honeLoss :
      ∀ i : ProjectionOrdered V,
        (active B i).card ≤ n - k i + 1 := by
    intro i
    exact planarStandardResidual_active_card_le_oneLayer
      hp hcap hn hdelta0 hdelta1 ht hlam i (cycles i)
  have hsize : Fintype.card (ProjectionOrdered V) ≤ 11 := by
    have hcardeq :
        Fintype.card (ProjectionOrdered V) = Fintype.card V := by
      let e : ProjectionOrdered V ≃ V :=
        { toFun := ProjectionOrdered.toOriginal
          invFun := ProjectionOrdered.ofOriginal
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact Fintype.card_congr e
    omega
  refine ⟨hexp, honeLoss, ?_⟩
  by_cases hd : netCollisionCertifiedDuplicateDebt B k hexp honeLoss = 0
  · exact Or.inl hd
  · exact Or.inr
      (net_collision_positive_duplicate_eleven_centres_twin_mass_le
        B k hexp honeLoss hstrict hsize (Nat.pos_of_ne_zero hd))

#print axioms planar_net_eleven_centres_duplicate_or_twin_mass_le

end ProjectionOrdered
end JSP000404Research
