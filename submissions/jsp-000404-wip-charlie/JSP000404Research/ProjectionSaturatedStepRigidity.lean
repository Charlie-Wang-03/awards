import JSP000404Research.ProjectionSaturatedBandEquality
import JSP000404Research.LinearBandGapStepTight
import Mathlib.Tactic

/-!
# Stepwise rigidity at saturated projected endpoints

ProjectionSaturatedBandEquality shows that a residual-active endpoint with
ExactProjectedBudget saturates the full local band-gap inequality.

The equality proof has no hidden slack: LinearBandGapStepTight therefore forces
every adjacent sorted local-direction step to be tight.

This file also records that an ordered edge u<v has the same local direction
value D.value u v when viewed from either endpoint, and that this value occurs
in every complete LocalDirectionCycle at both endpoints.  For a residual edge
in the standard residual colouring its natural floor is exactly n.

These facts are the local arithmetic input needed to compare the two endpoints
of a saturated--saturated overlap carrier.
-/

namespace JSP000404Research
namespace DirectionData
namespace LocalDirectionCycle

/-- Every incident local direction value occurs in a complete local cycle. -/
theorem localDirectionValue_mem_values
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (L : LocalDirectionCycle D i)
    (j : OtherVertex i) :
    D.localDirectionValue i j ∈ L.values := by
  have hjFin : j ∈ L.rays.toFinset := by
    rw [L.complete]
    simp
  have hj : j ∈ L.rays := by
    simpa using hjFin
  rw [LocalDirectionCycle.values, List.mem_map]
  exact ⟨j, hj, rfl⟩

/-- The same ordered edge contributes the same local direction value at its
two endpoints. -/
theorem edge_value_mem_both_localCycles
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t}
    {u v : V}
    (huv : u < v)
    (Lu : LocalDirectionCycle D u)
    (Lv : LocalDirectionCycle D v) :
    D.value u v ∈ Lu.values ∧
      D.value u v ∈ Lv.values := by
  let ju : OtherVertex u := ⟨v, ne_of_gt huv⟩
  let jv : OtherVertex v := ⟨u, ne_of_lt huv⟩
  have huMem :
      D.localDirectionValue u ju ∈ Lu.values :=
    Lu.localDirectionValue_mem_values ju
  have hvMem :
      D.localDirectionValue v jv ∈ Lv.values :=
    Lv.localDirectionValue_mem_values jv
  have huEq :
      D.localDirectionValue u ju = D.value u v := by
    unfold DirectionData.localDirectionValue
    simp [ju, huv, not_lt_of_ge huv.le]
  have hvEq :
      D.localDirectionValue v jv = D.value u v := by
    unfold DirectionData.localDirectionValue
    simp [jv, huv]
  constructor
  · simpa [huEq] using huMem
  · simpa [hvEq] using hvMem

/-- In the standard residual colouring, a residual edge has natural direction
floor exactly n. -/
theorem floor_edge_value_eq_top_of_standardResidual
    {V : Type*} [LinearOrder V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hwidth : t < (n : ℝ) + 1)
    {u v : V}
    (huv : u < v)
    (hres :
      OrderedEdgeColoring.IsResidual
        (standardResidualColoring D n hwidth) u v) :
    Nat.floor (D.value u v) = n := by
  have hx0 : 0 ≤ D.value u v := D.nonnegative huv
  have hxn :
      (n : ℝ) ≤ D.value u v :=
    standardResidual_value_ge_n
      D n hwidth huv hres
  have hxTop :
      D.value u v < (n : ℝ) + 1 :=
    (D.belowWidth huv).trans hwidth
  exact (Nat.floor_eq_iff hx0).2 ⟨hxn, hxTop⟩

end LocalDirectionCycle
end DirectionData

namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- Saturation gives the full stepwise-tight local cyclic profile, not merely
the wrap equality. -/
theorem genericProjection_saturated_stepwise_rigidity
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (htPos : 0 < t)
    (hlam : lam = Real.pi / t)
    (hwidth : t < (n : ℝ) + 1)
    (exponent : ProjectionOrdered V → ℕ)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hexpI : exponent i = centreExponent C t)
    (hsat :
      ExactProjectedBudget
        (genericResidualColoring hp hcap htPos hlam n hwidth)
        exponent i)
    (hres :
      residualCoord n ∈
        active
          (genericResidualColoring hp hcap htPos hlam n hwidth) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let D := genericDirectionData_sendov hp hcap htPos hlam
    let L := projectionCutLocalCycle hp hcap htPos hlam i C
    ∃ a xs,
      L.values = a :: xs ∧
      Nat.floor (xs.getLastD a) = n ∧
      InteriorBandGapTight a xs ∧
      excess (Nat.floor (a + t - xs.getLastD a)) =
        Nat.floor a := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let D := genericDirectionData_sendov hp hcap htPos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    genericResidualColoring hp hcap htPos hlam n hwidth
  let L := projectionCutLocalCycle hp hcap htPos hlam i C
  have heq :
      L.exponent + (D.incidentBands (n + 1) i).card = n + 1 :=
    genericProjection_saturated_local_band_equality
      hp hcap htPos hlam hwidth exponent i C
      hexpI hsat hres
  have htop :
      residualCoord n ∈ D.incidentBands (n + 1) i := by
    have hactiveEq :=
      standardResidual_active_eq_incidentBands_succ
        D n hwidth i
    have hres' : residualCoord n ∈ active B i := by
      simpa [B] using hres
    have hactiveEq' :
        active B i = D.incidentBands (n + 1) i := by
      simpa [B, D, genericResidualColoring] using hactiveEq
    rw [← hactiveEq']
    exact hres'
  obtain ⟨a, xs, hvalues⟩ :
      ∃ a xs, L.values = a :: xs := by
    cases h : L.values with
    | nil =>
        exact False.elim (L.values_nonempty h)
    | cons a xs =>
        exact ⟨a, xs, h⟩
  have haMem : a ∈ L.values := by
    rw [hvalues]
    simp
  have ha0 : 0 ≤ a := (L.value_mem_bounds haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using L.values_pairwise
  have hall :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact
      (L.value_mem_bounds
        (by simpa [hvalues] using hx)).2
  have hlast :
      Nat.floor (xs.getLastD a) = n :=
    localDirection_last_floor_eq_top_of_topBand_mem
      D L hwidth htop hvalues
  have hbands :=
    L.occupiedNatBands_values_card_eq_incidentBands_card
      (n + 1) (by
        push_cast
        exact le_of_lt hwidth)
  have heq' := heq
  rw [← hbands] at heq'
  unfold LocalDirectionCycle.exponent
    LocalDirectionCycle.gapQuotients at heq'
  rw [hvalues] at heq'
  have htight :
      InteriorBandGapTight a xs :=
    linear_cyclic_gapEquality_implies_stepwise_tight
      a xs ha0 hsorted hall hwidth heq'
  have hwrap :
      excess (Nat.floor (a + t - xs.getLastD a)) =
        Nat.floor a :=
    wrap_gap_excess_eq_floor_head_of_global_equality_top_last
      a xs ha0 hsorted hall hwidth heq' hlast
  exact ⟨a, xs, hvalues, hlast, htight, hwrap⟩

#print axioms DirectionData.LocalDirectionCycle.localDirectionValue_mem_values
#print axioms DirectionData.LocalDirectionCycle.edge_value_mem_both_localCycles
#print axioms DirectionData.LocalDirectionCycle.floor_edge_value_eq_top_of_standardResidual
#print axioms genericProjection_saturated_stepwise_rigidity

end ProjectionOrdered
end JSP000404Research
