import JSP000404Research.SaturatedWrapDescent
import JSP000404Research.ProjectionCutLocalCycle
import JSP000404Research.CyclicQuotientRotation
import Mathlib.Tactic

/-!
# Zero-unit steps are genuine quotient-zero gaps

A HasZeroQuotientUnitStep witness is an adjacent sorted local-direction step

  floor(b) = floor(a)+1,
  floor(b-a) = 0.

Hence zero occurs in the successive part of the local cyclic quotient list.

For the generic projection construction we can say more than the exponent
identity previously used: the entire quotient list of projectionCutLocalCycle
is exactly a cyclic rotation of the genuine canonical centre quotient list.
This follows by composing

* the explicit affine-unwrapped local value formula,
* affine invariance of cyclic gap quotients,
* projective-cut rotation of the normalized gap list, and
* quotientList commuting with List.rotate.

Consequently any local zero-unit step produces an actual quotient-zero gap in
the genuine centre cycle.
-/

namespace JSP000404Research

/-- A zero-quotient unit-band step contributes an actual zero entry to the
successive gap quotient list. -/
theorem zero_mem_successive_floor_gaps_of_hasZeroQuotientUnitStep
    (a : ℝ) (xs : List ℝ)
    (h : HasZeroQuotientUnitStep a xs) :
    0 ∈ (successiveDiffsFrom a xs).map Nat.floor := by
  induction xs generalizing a with
  | nil =>
      simp [HasZeroQuotientUnitStep] at h
  | cons b bs ih =>
      rw [hasZeroQuotientUnitStep_cons] at h
      simp only [successiveDiffsFrom, List.map_cons, List.mem_cons]
      rcases h with hhead | htail
      · exact Or.inl hhead.2
      · exact Or.inr (ih b htail)

/-- Therefore zero belongs to the whole local cyclic quotient list. -/
theorem zero_mem_linearCyclicGapQuotients_of_hasZeroQuotientUnitStep
    (t a : ℝ) (xs : List ℝ)
    (h : HasZeroQuotientUnitStep a xs) :
    0 ∈ linearCyclicGapQuotients t (a :: xs) := by
  have hz :=
    zero_mem_successive_floor_gaps_of_hasZeroQuotientUnitStep
      a xs h
  unfold linearCyclicGapQuotients
  exact List.mem_append_left _ hz

namespace ProjectionOrdered

open DirectionData

/-- Strong list-level form of the generic-projection representation bridge:
the local cyclic quotient list is the canonical centre quotient list rotated
by the projective-cut position. -/
theorem projectionCutLocalCycle_gapQuotients_eq_rotate
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (projectionCutLocalCycle hp hcap ht hlam i C).gapQuotients
      =
    (quotientList t C.gaps).rotate
      (projectionCutLowAngles hp i C).length := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let low := projectionCutLowAngles hp i C
  let high := projectionCutHighAngles hp i C
  let unwrapped :=
    high.map (fun theta => theta - Real.pi) ++ low
  let L :=
    projectionCutLocalCycle hp hcap ht hlam i C
  have hangles :
      C.angles = low ++ high := by
    simpa [low, high] using
      centreAngles_eq_cutLow_append_cutHigh hp i C
  have hne : low ++ high ≠ [] := by
    intro hnil
    apply C.angles_nonempty
    rw [hangles]
    exact hnil
  have hvalues :
      L.values =
        unwrapped.map
          (affineAngleValue
            (projectionAngleBase (genericProjectionSlope p))
            lam) := by
    simpa [L, low, high, unwrapped] using
      projectionCutLocalCycle_values_eq_affine_unwrapped
        hp hcap ht hlam i C
  unfold LocalDirectionCycle.gapQuotients
  rw [hvalues]
  rw [linearCyclicGapQuotients_affine_eq_quotientList
      (projectionAngleBase (genericProjectionSlope p))
      lam t ht hlam unwrapped]
  change
    quotientList t
      (normalizedProjectiveGaps
        (high.map (fun x => x - Real.pi) ++ low))
      =
    (quotientList t C.gaps).rotate low.length
  rw [normalizedProjectiveGaps_cut_rotate low high hne]
  rw [quotientList_rotate]
  have hgap :
      normalizedProjectiveGaps (low ++ high) = C.gaps := by
    rw [← hangles]
    rfl
  rw [hgap]

/-- Membership form: every local quotient is a genuine centre quotient up to
the harmless cyclic cut rotation. -/
theorem mem_centreQuotients_of_mem_projectionCutLocalQuotients
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {q : ℕ}
    (hq :
      q ∈
        (projectionCutLocalCycle
          hp hcap ht hlam i C).gapQuotients) :
    q ∈ quotientList t C.gaps := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  rw [projectionCutLocalCycle_gapQuotients_eq_rotate
      hp hcap ht hlam i C] at hq
  simpa using hq

/-- Main zero-gap bridge from saturated local step rigidity back to the
genuine centre quotient cycle. -/
theorem centreQuotient_has_zero_of_projection_zeroUnitStep
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {a : ℝ} {xs : List ℝ}
    (hvalues :
      (projectionCutLocalCycle
        hp hcap ht hlam i C).values = a :: xs)
    (hstep : HasZeroQuotientUnitStep a xs) :
    0 ∈ quotientList t C.gaps := by
  apply mem_centreQuotients_of_mem_projectionCutLocalQuotients
    hp hcap ht hlam i C
  unfold LocalDirectionCycle.gapQuotients
  rw [hvalues]
  exact zero_mem_linearCyclicGapQuotients_of_hasZeroQuotientUnitStep
    t a xs hstep

#print axioms zero_mem_successive_floor_gaps_of_hasZeroQuotientUnitStep
#print axioms zero_mem_linearCyclicGapQuotients_of_hasZeroQuotientUnitStep
#print axioms projectionCutLocalCycle_gapQuotients_eq_rotate
#print axioms centreQuotient_has_zero_of_projection_zeroUnitStep

end ProjectionOrdered
end JSP000404Research
