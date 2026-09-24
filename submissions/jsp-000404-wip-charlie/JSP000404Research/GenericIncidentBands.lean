import JSP000404Research.GenericCutExponentInvariant
import JSP000404Research.GenericForwardAngleLift
import JSP000404Research.IncidentBandLabels
import Mathlib.Tactic

/-!
# Generic line values recover the actual incident standard bands

The generic projective-line block construction is indexed by original
neighbours of i.toOriginal, while generic DirectionData lives on the wrapper
ProjectionOrdered V.

The wrapper is definitionally the same underlying vertex type.  This file
builds the natural neighbour equivalence and proves that the unordered
incident DirectionData value is exactly

  (genericLineAngle - projectionAngleBase) / lambda.

Therefore the distinct natural floors of the normalized generic-cut angle list
are exactly the local incidentBands of the standard unit-band colouring.
-/

namespace JSP000404Research
namespace ProjectionOrdered

def toProjectionOther
    {V : Type*}
    (i : ProjectionOrdered V)
    (j : OtherVertex i.toOriginal) :
    OtherVertex i :=
  ⟨ofOriginal j.1, by
    intro h
    apply j.2
    exact congrArg toOriginal h⟩

def fromProjectionOther
    {V : Type*}
    (i : ProjectionOrdered V)
    (j : OtherVertex i) :
    OtherVertex i.toOriginal :=
  ⟨j.1.toOriginal, by
    intro h
    apply j.2
    apply toOriginal_injective
    simpa using h⟩

@[simp] theorem from_toProjectionOther
    {V : Type*}
    (i : ProjectionOrdered V)
    (j : OtherVertex i.toOriginal) :
    fromProjectionOther i (toProjectionOther i j) = j := by
  apply Subtype.ext
  rfl

@[simp] theorem to_fromProjectionOther
    {V : Type*}
    (i : ProjectionOrdered V)
    (j : OtherVertex i) :
    toProjectionOther i (fromProjectionOther i j) = j := by
  apply Subtype.ext
  exact ofOriginal_toOriginal j.1

noncomputable def genericCutOriginalRays
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    List (OtherVertex i.toOriginal) :=
  genericNegativeRays hp i ++
    genericNonnegativeRays hp i

theorem genericCutOriginalRays_complete
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    (genericCutOriginalRays hp i).toFinset =
      Finset.univ := by
  classical
  ext j
  by_cases hneg :
      genericLineAngleAt hp i j < 0
  · simp [genericCutOriginalRays,
      genericNegativeSet, genericNonnegativeSet,
      hneg]
  · simp [genericCutOriginalRays,
      genericNegativeSet, genericNonnegativeSet,
      hneg]

noncomputable def genericCutProjectionRays
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    List (OtherVertex i) :=
  (genericCutOriginalRays hp i).map
    (toProjectionOther i)

theorem genericCutProjectionRays_complete
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) :
    (genericCutProjectionRays hp i).toFinset =
      Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro j
  rw [List.mem_toFinset, genericCutProjectionRays,
      List.mem_map]
  let jo := fromProjectionOther i j
  refine ⟨jo, ?_, ?_⟩
  · have hjoFin :
        jo ∈ (genericCutOriginalRays hp i).toFinset := by
      rw [genericCutOriginalRays_complete hp i]
      simp
    simpa using hjoFin
  · exact to_fromProjectionOther i j

/-- Unordered incident value equals the normalized generic line angle. -/
theorem generic_incidentValueAt_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (j : OtherVertex i.toOriginal) :
    @DirectionData.incidentValueAt
        (ProjectionOrdered V)
        (projectionLinearOrder hp)
        t
        (genericDirectionData_sendov hp hcap ht hlam)
        i
        (toProjectionOther i j)
      =
    (genericLineAngleAt hp i j -
      projectionAngleBase (genericProjectionSlope p)) / lam := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let jp : OtherVertex i := toProjectionOther i j
  by_cases hji : jp.1 < i
  · have hijNot : ¬ i < jp.1 :=
      not_lt_of_ge hji.le
    simp [DirectionData.incidentValueAt, jp,
      genericLineAngleAt, genericLineAngle,
      hji, hijNot,
      genericDirectionData_sendov_value]
  · have hij : i < jp.1 :=
      lt_of_le_of_ne (not_lt.mp hji) jp.2.symm
    simp [DirectionData.incidentValueAt, jp,
      genericLineAngleAt, genericLineAngle,
      hji, hij,
      genericDirectionData_sendov_value]

noncomputable def genericNormalizedCutAngles
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (lam : ℝ)
    (i : ProjectionOrdered V) : List ℝ :=
  (genericCutAngles hp i).map
    (fun theta =>
      (theta - projectionAngleBase
        (genericProjectionSlope p)) / lam)

/-- The normalized generic cut list is exactly the unordered incident-value
list attached to the complete projection-neighbour enumeration. -/
theorem genericNormalizedCutAngles_eq_incidentValues
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V) :
    genericNormalizedCutAngles hp lam i =
      (genericCutProjectionRays hp i).map
        (@DirectionData.incidentValueAt
          (ProjectionOrdered V)
          (projectionLinearOrder hp)
          t
          (genericDirectionData_sendov hp hcap ht hlam)
          i) := by
  unfold genericNormalizedCutAngles
  unfold genericCutAngles genericCutProjectionRays
  unfold genericNegativeAngles genericNonnegativeAngles
  simp only [List.map_append, List.map_map]
  apply congrArg₂ (· ++ ·)
  · apply List.map_congr_left
    intro j hj
    symm
    exact generic_incidentValueAt_eq
      hp hcap ht hlam i j
  · apply List.map_congr_left
    intro j hj
    symm
    exact generic_incidentValueAt_eq
      hp hcap ht hlam i j

/-- Distinct generic normalized floor labels are exactly the true local
incident standard bands. -/
theorem genericNormalizedCut_floorLabels_card_eq_incidentBands
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (n : ℕ)
    (hwidth : t ≤ (n + 1 : ℕ))
    (i : ProjectionOrdered V) :
    ((genericNormalizedCutAngles hp lam i).map
        Nat.floor).toFinset.card
      =
    (@DirectionData.incidentBands
      (ProjectionOrdered V)
      (projectionLinearOrder hp)
      t
      (genericDirectionData_sendov hp hcap ht hlam)
      (n + 1) i).card := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let D :=
    genericDirectionData_sendov hp hcap ht hlam
  rw [genericNormalizedCutAngles_eq_incidentValues
      hp hcap ht hlam i]
  exact DirectionData.incidentFloorLabels_card_eq_incidentBands_card
    D (n + 1)
    (by exact_mod_cast hwidth)
    i
    (genericCutProjectionRays hp i)
    (genericCutProjectionRays_complete hp i)

#print axioms generic_incidentValueAt_eq
#print axioms genericNormalizedCutAngles_eq_incidentValues
#print axioms genericNormalizedCut_floorLabels_card_eq_incidentBands

end ProjectionOrdered
end JSP000404Research
