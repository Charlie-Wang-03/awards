
import JSP000404Research.ProjectionResidualHardRemainder
import JSP000404Research.LinearBandGapEquality
import JSP000404Research.ResidualSaturationBridge
import Mathlib.Tactic

/-!
# Saturated residual endpoints are equality cases of the band-gap theorem

For the actual generic-projection standard residual colouring, a residual-active
vertex with ExactProjectedBudget satisfies

  centreExponent + card(active) = n+1.

Via ProjectionCutLocalCycle this is exactly equality in the one-dimensional
linear cyclic band-gap inequality.

Because the residual colour is active, the top unit band n occurs among the
local direction values, so the last sorted local value has natural floor n.
LinearBandGapEquality then forces the cyclic wrap-gap excess to equal the first
occupied-band index.

This is a concrete rigidity certificate for every saturated endpoint of a hard
residual overlap.
-/

namespace JSP000404Research
namespace DirectionData

/-- In a sorted nonempty list, every member is at most the final element. -/
theorem mem_le_getLastD_of_pairwise
    {a x : ℝ} {xs : List ℝ}
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hx : x ∈ a :: xs) :
    x ≤ xs.getLastD a := by
  induction xs generalizing a with
  | nil =>
      simp at hx
      subst x
      simp
  | cons b bs ih =>
      have hp := List.pairwise_cons.mp hsorted
      simp only [List.mem_cons] at hx
      rcases hx with hxa | hxTail
      · subst x
        exact head_le_getLastD_of_pairwise a (b :: bs) hsorted
      · have htail :
          (b :: bs).Pairwise (· ≤ ·) :=
        hp.2
        have hle :
            x ≤ bs.getLastD b :=
          ih htail hxTail
        simpa using hle

/-- If the top band n is incident to a complete local cycle, the last sorted
local value has floor n. -/
theorem localDirection_last_floor_eq_top_of_topBand_mem
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    {i : V}
    (L : LocalDirectionCycle D i)
    (ht : t < (n : ℝ) + 1)
    (htop :
      residualCoord n ∈ D.incidentBands (n + 1) i)
    {a : ℝ} {xs : List ℝ}
    (hvalues : L.values = a :: xs) :
    Nat.floor (xs.getLastD a) = n := by
  have hex :
      ∃ j : OtherVertex i,
        Nat.floor (D.localDirectionValue i j) = n := by
    have h :=
      (mem_incidentBands_iff_exists_local_floor
        D (n + 1) i (residualCoord n)).1 htop
    simpa [residualCoord] using h
  obtain ⟨j, hjfloor⟩ := hex
  have hjRay : j ∈ L.rays := by
    have hjFin : j ∈ L.rays.toFinset := by
      rw [L.complete]
      simp
    simpa using hjFin
  have hjVal :
      D.localDirectionValue i j ∈ L.values := by
    rw [LocalDirectionCycle.values, List.mem_map]
    exact ⟨j, hjRay, rfl⟩
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using L.values_pairwise
  have hjVal' :
      D.localDirectionValue i j ∈ a :: xs := by
    simpa [hvalues] using hjVal
  have hleVal :
      D.localDirectionValue i j ≤ xs.getLastD a :=
    mem_le_getLastD_of_pairwise hsorted hjVal'
  have hfloorLower :
      n ≤ Nat.floor (xs.getLastD a) := by
    rw [← hjfloor]
    exact Nat.floor_mono hleVal
  have hlastMem :
      xs.getLastD a ∈ L.values := by
    rw [hvalues]
    exact List.getLastD_mem_cons a xs
  have hlastBounds :=
    L.value_mem_bounds hlastMem
  have hlastTop :
      Nat.floor (xs.getLastD a) < n + 1 := by
    apply (Nat.floor_lt hlastBounds.1).2
    have hreal :
        xs.getLastD a < ((n + 1 : ℕ) : ℝ) := by
      push_cast
      exact hlastBounds.2.trans ht
    exact hreal
  omega

end DirectionData

namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- A saturated residual-active concrete centre attains equality in the full
(n+1)-band local capacity.  The ambient exponent function is only used at the
chosen centre, where it is identified with the genuine centre exponent. -/
theorem genericProjection_saturated_local_band_equality
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
    L.exponent + (D.incidentBands (n + 1) i).card = n + 1 := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let D := genericDirectionData_sendov hp hcap htPos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    genericResidualColoring hp hcap htPos hlam n hwidth
  let L := projectionCutLocalCycle hp hcap htPos hlam i C
  have hsat' : ExactProjectedBudget B exponent i := by
    simpa [B] using hsat
  have hres' : residualCoord n ∈ active B i := by
    simpa [B] using hres
  have hactiveEq :=
    active_card_eq_exact_one_loss_of_residual_saturated
      B exponent hsat' hres'
  have hactiveBands :
      (active B i).card =
        (D.incidentBands (n + 1) i).card := by
    have h :=
      standardResidual_active_eq_incidentBands_succ
        D n hwidth i
    simpa [B, D, genericResidualColoring] using
      congrArg Finset.card h
  have hagree :
      L.exponent = centreExponent C t :=
    projectionCutLocalCycle_exponent_eq_centreExponent
      hp hcap htPos hlam i C
  have hretN :
      (retainedActive B i).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive B i)
  have hexpLe : exponent i ≤ n := by
    unfold ExactProjectedBudget projectedFree at hsat'
    omega
  rw [hagree, ← hactiveBands, ← hexpI]
  omega

/-- Concrete wrap rigidity at a saturated residual-active centre. -/
theorem genericProjection_saturated_wrap_rigidity
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
  have ha0 := (L.value_mem_bounds haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using L.values_pairwise
  have hall :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact (L.value_mem_bounds
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
  refine ⟨a, xs, hvalues, hlast, ?_⟩
  exact wrap_gap_excess_eq_floor_head_of_global_equality_top_last
    a xs ha0 hsorted hall hwidth heq' hlast

#print axioms mem_le_getLastD_of_pairwise
#print axioms localDirection_last_floor_eq_top_of_topBand_mem
#print axioms genericProjection_saturated_local_band_equality
#print axioms genericProjection_saturated_wrap_rigidity

end ProjectionOrdered
end JSP000404Research
