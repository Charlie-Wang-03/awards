import JSP000404Research.ProjectionSaturatedStepRigidity
import JSP000404Research.SaturatedWrapDescent
import JSP000404Research.ProjectionSaturatedOverlapRigidity
import Mathlib.Tactic

/-!
# Lower-branch dichotomy at a saturated projected endpoint

At a saturated residual-active endpoint, ProjectionSaturatedStepRigidity gives
a sorted stepwise-tight local cyclic profile

  a :: xs

with top final floor n and saturated wrap equality.

In the lower branch delta<1/2, either the first occupied band is zero, or
SaturatedWrapDescent forces at least one adjacent unit-band step.

For a saturated--saturated overlap carrier u<v, both endpoints satisfy this
dichotomy and the same residual direction value D.value u v occurs in both
local cycles with natural floor n.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- Concrete lower-branch endpoint dichotomy. -/
theorem genericProjection_saturated_zeroFirst_or_unitStep
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (htEq : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (exponent : ProjectionOrdered V → ℕ)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hexpI : exponent i = centreExponent C t)
    (hsat :
      ExactProjectedBudget
        (genericResidualColoring
          hp hcap
          (sendov_scale_pos hn hdelta0 htEq)
          hlam n
          (by
            rw [htEq]
            linarith))
        exponent i)
    (hres :
      residualCoord n ∈
        active
          (genericResidualColoring
            hp hcap
            (sendov_scale_pos hn hdelta0 htEq)
            hlam n
            (by
              rw [htEq]
              linarith))
          i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let D :=
      genericDirectionData_sendov
        hp hcap (sendov_scale_pos hn hdelta0 htEq) hlam
    let L :=
      projectionCutLocalCycle
        hp hcap (sendov_scale_pos hn hdelta0 htEq)
        hlam i C
    ∃ a xs,
      L.values = a :: xs ∧
      Nat.floor (xs.getLastD a) = n ∧
      InteriorBandGapTight a xs ∧
      excess (Nat.floor (a + t - xs.getLastD a)) =
        Nat.floor a ∧
      (Nat.floor a = 0 ∨
        HasZeroQuotientUnitStep a xs) := by
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
  let L :=
    projectionCutLocalCycle
      hp hcap htPos hlam i C
  obtain ⟨a, xs, hvalues, hlast, htight, hwrap⟩ :=
    genericProjection_saturated_stepwise_rigidity
      hp hcap htPos hlam hwidth
      exponent i C hexpI hsat hres
  have haMem : a ∈ L.values := by
    rw [hvalues]
    simp
  have ha0 : 0 ≤ a :=
    (L.value_mem_bounds haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using L.values_pairwise
  have hall :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact
      (L.value_mem_bounds
        (by simpa [hvalues] using hx)).2
  refine ⟨a, xs, hvalues, hlast, htight, hwrap, ?_⟩
  by_cases hzero : Nat.floor a = 0
  · exact Or.inl hzero
  · right
    have hpos : 1 ≤ Nat.floor a := by omega
    exact saturated_wrap_positive_first_has_zeroUnitStep
      xs ha0 hsorted hall htEq hlast hwrap
      hpos hdeltaHalf htight

/-- Both endpoints of a saturated--saturated overlap satisfy the lower-branch
zero-first-or-unit-step dichotomy, while sharing one common top-band edge
value. -/
theorem saturatedSaturatedWord_has_common_top_and_endpoint_dichotomies
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
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
      Nat.floor (D.value u v) = n ∧
      D.value u v ∈
        (projectionCutLocalCycle
          hp hcap (sendov_scale_pos hn hdelta0 htEq)
          hlam u (C u)).values ∧
      D.value u v ∈
        (projectionCutLocalCycle
          hp hcap (sendov_scale_pos hn hdelta0 htEq)
          hlam v (C v)).values ∧
      (
        ∃ a xs,
          (projectionCutLocalCycle
            hp hcap (sendov_scale_pos hn hdelta0 htEq)
            hlam u (C u)).values = a :: xs ∧
          Nat.floor (xs.getLastD a) = n ∧
          InteriorBandGapTight a xs ∧
          excess (Nat.floor (a + t - xs.getLastD a)) =
            Nat.floor a ∧
          (Nat.floor a = 0 ∨
            HasZeroQuotientUnitStep a xs)
      )
      ∧
      (
        ∃ a xs,
          (projectionCutLocalCycle
            hp hcap (sendov_scale_pos hn hdelta0 htEq)
            hlam v (C v)).values = a :: xs ∧
          Nat.floor (xs.getLastD a) = n ∧
          InteriorBandGapTight a xs ∧
          excess (Nat.floor (a + t - xs.getLastD a)) =
            Nat.floor a ∧
          (Nat.floor a = 0 ∨
            HasZeroQuotientUnitStep a xs)
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
  obtain ⟨u, v, huv, hres, huWord, hvWord, _huniq⟩ :=
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
  have huDich :=
    genericProjection_saturated_zeroFirst_or_unitStep
      hp hcap hn hdelta0 hdeltaHalf htEq hlam
      exponent u (C u) rfl
      (by simpa [B] using huSat)
      (by simpa [B] using hactive.1)
  have hvDich :=
    genericProjection_saturated_zeroFirst_or_unitStep
      hp hcap hn hdelta0 hdeltaHalf htEq hlam
      exponent v (C v) rfl
      (by simpa [B] using hvSat)
      (by simpa [B] using hactive.2)
  let Lu :=
    projectionCutLocalCycle
      hp hcap htPos hlam u (C u)
  let Lv :=
    projectionCutLocalCycle
      hp hcap htPos hlam v (C v)
  have hcommon :=
    DirectionData.LocalDirectionCycle.edge_value_mem_both_localCycles
      (D := D) huv Lu Lv
  have hresStd :
      IsResidual (standardResidualColoring D n hwidth) u v := by
    simpa [B, D, genericResidualColoring] using hres
  have hfloor :
      Nat.floor (D.value u v) = n :=
    DirectionData.LocalDirectionCycle.floor_edge_value_eq_top_of_standardResidual
      D hwidth huv hresStd
  refine ⟨u, v, huv, hres, hfloor, ?_, ?_, ?_, ?_⟩
  · simpa [Lu] using hcommon.1
  · simpa [Lv] using hcommon.2
  · simpa [Lu] using huDich
  · simpa [Lv] using hvDich

#print axioms genericProjection_saturated_zeroFirst_or_unitStep
#print axioms saturatedSaturatedWord_has_common_top_and_endpoint_dichotomies

end ProjectionOrdered
end JSP000404Research
