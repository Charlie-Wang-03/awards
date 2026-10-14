import JSP000404Research.PlanarNetNineCentreTwinTradeoff
import JSP000404Research.ResidualNetCollisionElevenCentreTwinCap
import Mathlib.Tactic

/-!
# True planar AngleCap eleven-centre NET / terminal TWIN count tradeoff

This is a geometric specialization of the source-native carrier matching
bound: if there are at most ELEVEN original centres, either genuine
NET diagonal-duplicate debt is zero, or at most ONE original terminal
equal-exponent TWIN rigid hard carrier exists.

The original centre projective cycles and the genuine planar standard
residual colouring supply the necessary exponent and one-layer premises.
This constrains carrier cardinality, NOT dyadic twin mass, does not
produce Boolean holes, and does not resolve the unrestricted six-source
global payment.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_net_eleven_centres_duplicate_or_twin_card_le_one
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
          (netTwinRigidCarriers B k).card ≤ 1 := by
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
          (netTwinRigidCarriers B k).card ≤ 1
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
      (net_collision_positive_duplicate_eleven_centres_twin_card_le_one
        B k hexp honeLoss hsize (Nat.pos_of_ne_zero hd))

#print axioms planar_net_eleven_centres_duplicate_or_twin_card_le_one

end ProjectionOrdered
end JSP000404Research
