import JSP000404Research.PlanarOverweightRealResidualCollision
import JSP000404Research.ProjectionSaturatedEndpointDichotomy
import JSP000404Research.ProjectionSaturatedStepRigidity
import Mathlib.Tactic

/-!
# Actual overweight planar carrier: top-band edge plus rigid phase witness

A truly overweight lower-branch configuration either has a projected-loss
centre, or has a genuine residual u<v edge carrying a common completion word.

In the second case, one actual endpoint is exactly projected-saturated.
The incident residual edge has normalized natural floor n at both endpoints.
The saturated endpoint has a sorted local cycle with:
* last occupied floor n;
* every interior band-gap step tight;
* wrap gap equality;
* either first occupied band zero, or a zero-quotient unit-band step.

This connects an ACTUAL cross-centre collision to the already established
local geometry. It is not yet a global injection/payment of residual words,
and leaves the original lower-branch conjecture open.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- A lower-branch planar counterexample must exhibit either a projected
loss or an actual hard residual collision with a rigid saturated end. -/
theorem planar_overweight_loss_or_hard_carrier_phase_witness
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
    (hover :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      2 ^ n < ∑ i : ProjectionOrdered V,
        2 ^ centreExponent (cycles i) t) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let hpos : 0 < t := sendov_scale_pos hn hdelta0 ht
    let hwidth : t < (n : ℝ) + 1 := by rw [ht]; linarith
    let D := genericDirectionData_sendov hp hcap hpos hlam
    let B := standardResidualColoring D n (by exact_mod_cast hwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    (∃ i : ProjectionOrdered V,
      i ∈ projectedLossVertices B k) ∨
      (∃ (u v : ProjectionOrdered V) (word : Fin n → Bool),
        u < v ∧
        IsResidual B u v ∧
        word ∈ retainedCompletionWords B u ∧
        word ∈ retainedCompletionWords B v ∧
        Nat.floor (D.value u v) = n ∧
        ∃ i : ProjectionOrdered V,
          (i = u ∨ i = v) ∧
          k i = projectedFree B i ∧
          ∃ a : ℝ, ∃ xs : List ℝ,
            (projectionCutLocalCycle hp hcap hpos hlam
              i (cycles i)).values = a :: xs ∧
            Nat.floor (xs.getLastD a) = n ∧
            InteriorBandGapTight a xs ∧
            excess (Nat.floor (a + t - xs.getLastD a)) =
              Nat.floor a ∧
            (Nat.floor a = 0 ∨ HasZeroQuotientUnitStep a xs)) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hpos : 0 < t := sendov_scale_pos hn hdelta0 ht
  have hwidth : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  let D : DirectionData (ProjectionOrdered V) t :=
    genericDirectionData_sendov hp hcap hpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  change
    (∃ i : ProjectionOrdered V,
      i ∈ projectedLossVertices B k) ∨
      (∃ (u v : ProjectionOrdered V) (word : Fin n → Bool),
        u < v ∧
        IsResidual B u v ∧
        word ∈ retainedCompletionWords B u ∧
        word ∈ retainedCompletionWords B v ∧
        Nat.floor (D.value u v) = n ∧
        ∃ i : ProjectionOrdered V,
          (i = u ∨ i = v) ∧
          k i = projectedFree B i ∧
          ∃ a : ℝ, ∃ xs : List ℝ,
            (projectionCutLocalCycle hp hcap hpos hlam
              i (cycles i)).values = a :: xs ∧
            Nat.floor (xs.getLastD a) = n ∧
            InteriorBandGapTight a xs ∧
            excess (Nat.floor (a + t - xs.getLastD a)) =
              Nat.floor a ∧
            (Nat.floor a = 0 ∨ HasZeroQuotientUnitStep a xs))
  have hbase :=
    planar_overweight_has_loss_or_real_saturated_residual_collision
      hp hcap hpos hlam hwidth cycles hover
  change
    (∃ i : ProjectionOrdered V,
      i ∈ projectedLossVertices B k) ∨
      (∃ (u v : ProjectionOrdered V) (word : Fin n → Bool),
        u < v ∧
        IsResidual B u v ∧
        word ∈ retainedCompletionWords B u ∧
        word ∈ retainedCompletionWords B v ∧
        (k u = projectedFree B u ∨
          k v = projectedFree B v)) at hbase
  rcases hbase with hloss | hcarrier
  · exact Or.inl hloss
  · right
    obtain ⟨u,v,word,huv,hres,huWord,hvWord,hsat⟩ := hcarrier
    have hfloor : Nat.floor (D.value u v) = n :=
      DirectionData.LocalDirectionCycle.floor_edge_value_eq_top_of_standardResidual
        D hwidth huv hres
    have hactive :=
      residualCoord_mem_active_of_isResidual B huv hres
    have hrigid (i : ProjectionOrdered V)
        (hki : k i = projectedFree B i)
        (hiActive : residualCoord n ∈ active B i) :
        ∃ a : ℝ, ∃ xs : List ℝ,
          (projectionCutLocalCycle hp hcap hpos hlam
            i (cycles i)).values = a :: xs ∧
          Nat.floor (xs.getLastD a) = n ∧
          InteriorBandGapTight a xs ∧
          excess (Nat.floor (a + t - xs.getLastD a)) =
            Nat.floor a ∧
          (Nat.floor a = 0 ∨ HasZeroQuotientUnitStep a xs) := by
      have hbudget :
          ExactProjectedBudget
            (genericResidualColoring hp hcap hpos hlam n hwidth)
            k i := by
        simpa [ExactProjectedBudget, B, D, genericResidualColoring]
          using hki
      have hresidual :
          residualCoord n ∈
            active
              (genericResidualColoring hp hcap hpos hlam n hwidth)
              i := by
        simpa [B, D, genericResidualColoring] using hiActive
      simpa using
        (genericProjection_saturated_zeroFirst_or_unitStep
          hp hcap hn hdelta0 hdeltaHalf ht hlam
          k i (cycles i) rfl hbudget hresidual)
    refine ⟨u, v, word, huv, hres, huWord, hvWord, hfloor, ?_⟩
    rcases hsat with huSat | hvSat
    · exact ⟨u, Or.inl rfl, huSat, hrigid u huSat hactive.1⟩
    · exact ⟨v, Or.inr rfl, hvSat, hrigid v hvSat hactive.2⟩

#print axioms planar_overweight_loss_or_hard_carrier_phase_witness

end ProjectionOrdered
end JSP000404Research
