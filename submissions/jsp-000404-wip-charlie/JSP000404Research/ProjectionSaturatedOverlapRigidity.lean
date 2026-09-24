
import JSP000404Research.ProjectionSaturatedBandEquality
import JSP000404Research.ResidualSaturatedOverlapDecomposition
import Mathlib.Tactic

/-!
# Concrete planar rigidity of a saturated--saturated overlap word

Take the actual generic-projection standard residual colouring of a planar
lower-branch Sendov configuration.

A word in saturatedSaturatedOverlapWords has a unique ordered residual carrier
u<v.  Both endpoints have ExactProjectedBudget and the residual colour is
active at both.

ProjectionSaturatedBandEquality therefore applies independently at u and v.
Consequently both genuine centre cycles admit local cut-rotated value lists

  a_u :: xs_u,
  a_v :: xs_v

whose last occupied floor is the residual top band n and whose cyclic wrap
excess is exactly the first occupied-band index.

This is the direct bridge from the final Boolean hard remainder back to the
actual centre-gap geometry.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- Every concrete saturated--saturated hard word has a unique residual
carrier whose two endpoints both satisfy the saturated wrap rigidity. -/
theorem saturatedSaturatedWord_has_two_wrap_rigid_endpoints
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (htEq : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {word : Fin n → Bool}
    (hword :
      let B :=
        genericResidualColoring
          hp hcap
          (sendov_scale_pos hn hdelta0 htEq)
          hlam n
          (by
            rw [htEq]
            linarith)
      let exponent :=
        fun i : ProjectionOrdered V =>
          centreExponent (C i) t
      word ∈ saturatedSaturatedOverlapWords B exponent) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let D :=
      genericDirectionData_sendov
        hp hcap (sendov_scale_pos hn hdelta0 htEq) hlam
    let B :=
      genericResidualColoring
        hp hcap (sendov_scale_pos hn hdelta0 htEq)
        hlam n
        (by
          rw [htEq]
          linarith)
    let exponent :=
      fun i : ProjectionOrdered V =>
        centreExponent (C i) t
    ∃ u v : ProjectionOrdered V,
      u < v ∧
      IsResidual B u v ∧
      word ∈ retainedCompletionWords B u ∧
      word ∈ retainedCompletionWords B v ∧
      (
        ∃ a xs,
          (projectionCutLocalCycle
            hp hcap (sendov_scale_pos hn hdelta0 htEq)
            hlam u (C u)).values = a :: xs ∧
          Nat.floor (xs.getLastD a) = n ∧
          excess (Nat.floor (a + t - xs.getLastD a)) =
            Nat.floor a
      )
      ∧
      (
        ∃ a xs,
          (projectionCutLocalCycle
            hp hcap (sendov_scale_pos hn hdelta0 htEq)
            hlam v (C v)).values = a :: xs ∧
          Nat.floor (xs.getLastD a) = n ∧
          excess (Nat.floor (a + t - xs.getLastD a)) =
            Nat.floor a
      ) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htPos :
      0 < t :=
    sendov_scale_pos hn hdelta0 htEq
  have hwidth :
      t < (n : ℝ) + 1 := by
    rw [htEq]
    linarith
  let D :=
    genericDirectionData_sendov hp hcap htPos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    genericResidualColoring hp hcap htPos hlam n hwidth
  let exponent : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (C i) t
  have hword' :
      word ∈ saturatedSaturatedOverlapWords B exponent := by
    simpa [B, exponent] using hword
  have hsatData :=
    (mem_saturatedSaturatedOverlapWords
      B exponent word).1 hword'
  obtain ⟨u, v, huv, hres, huWord, hvWord, huniq⟩ :=
    exists_ordered_residual_pair_of_overlapWord
      B hsatData.1
  have huSat :
      ExactProjectedBudget B exponent u :=
    hsatData.2 u huWord
  have hvSat :
      ExactProjectedBudget B exponent v :=
    hsatData.2 v hvWord
  have hactive :=
    residualCoord_mem_active_of_isResidual
      B huv hres
  have huRigid :=
    genericProjection_saturated_wrap_rigidity
      hp hcap htPos hlam hwidth exponent
      u (C u) rfl
      (by simpa [B] using huSat)
      (by simpa [B] using hactive.1)
  have hvRigid :=
    genericProjection_saturated_wrap_rigidity
      hp hcap htPos hlam hwidth exponent
      v (C v) rfl
      (by simpa [B] using hvSat)
      (by simpa [B] using hactive.2)
  exact ⟨u, v, huv, hres, huWord, hvWord,
    huRigid, hvRigid⟩

#print axioms saturatedSaturatedWord_has_two_wrap_rigid_endpoints

end ProjectionOrdered
end JSP000404Research
