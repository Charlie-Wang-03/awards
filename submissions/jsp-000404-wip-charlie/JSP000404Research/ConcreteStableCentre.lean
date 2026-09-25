
import JSP000404Research.ConcreteDeletionStableSplit
import JSP000404Research.ConcreteCentreDeletionMonotone
import Mathlib.Tactic

/-!
# Concrete deletion-stable centres

A concrete centre is unit-stable when deleting any other top-level vertex
never raises its Sendov exponent by a full unit.

This is exactly the geometric property selected by the canonical deletion
bonus argument at a maximal-exponent centre of an uncompensated configuration.

ConcreteDeletionStableSplit then converts this global deletion stability into
a local quotient statement at every ray: the two cyclic quotient gaps adjacent
to that ray cannot both be positive.
-/

namespace JSP000404Research

def ConcreteDeletionUnitStable
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) : Prop :=
  ∀ (r : V) (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir))),
    ¬ centreExponent C t + 1 ≤
      centreExponent
        (C.restrictDelete r hir hother) t

/-- Every split at an actual deleted ray of a concrete stable centre has a
zero adjacent quotient on at least one side. -/
theorem stableCentre_adjacent_zero_at_split
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ}
    (ht : 0 ≤ t)
    (hstable : ConcreteDeletionUnitStable C t)
    (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    (pre post : List (OtherVertex i))
    (hsplit :
      C.rays =
        pre ++ deletedParentRay r i hir :: post) :
    match pre, post with
    | [], [] => True
    | [], b :: bs =>
        Nat.floor
          (t * ((rayThetaAt hp i b -
            rayThetaAt hp i (deletedParentRay r i hir)) /
              Real.pi)) = 0
        ∨
        Nat.floor
          (t * ((rayThetaAt hp i (deletedParentRay r i hir) +
            Real.pi -
            (bs.map (rayThetaAt hp i)).getLastD
              (rayThetaAt hp i b)) / Real.pi)) = 0
    | first :: mid, [] =>
        Nat.floor
          (t * ((rayThetaAt hp i (deletedParentRay r i hir) -
            (mid.map (rayThetaAt hp i)).getLastD
              (rayThetaAt hp i first)) / Real.pi)) = 0
        ∨
        Nat.floor
          (t * ((rayThetaAt hp i first + Real.pi -
            rayThetaAt hp i (deletedParentRay r i hir)) /
              Real.pi)) = 0
    | first :: mid, next :: tail =>
        Nat.floor
          (t * ((rayThetaAt hp i (deletedParentRay r i hir) -
            (mid.map (rayThetaAt hp i)).getLastD
              (rayThetaAt hp i first)) / Real.pi)) = 0
        ∨
        Nat.floor
          (t * ((rayThetaAt hp i next -
            rayThetaAt hp i (deletedParentRay r i hir)) /
              Real.pi)) = 0 := by
  exact adjacent_zero_of_no_unit_gain
    C hir hother pre post hsplit ht
    (hstable r hir hother)

/-- Stronger negative form: no split of a concrete stable centre has both
adjacent quotient gaps positive. -/
theorem stableCentre_not_bothAdjacentPositive_at_split
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i r : V}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ}
    (ht : 0 ≤ t)
    (hstable : ConcreteDeletionUnitStable C t)
    (hir : i ≠ r)
    (hother :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    (pre post : List (OtherVertex i))
    (hsplit :
      C.rays =
        pre ++ deletedParentRay r i hir :: post) :
    ¬ ParentSplitBothAdjacentPositive
      C hir pre post t := by
  exact not_bothAdjacentPositive_of_no_unit_gain
    C hir hother pre post hsplit ht
    (hstable r hir hother)

/-- Under concrete deletion monotonicity, stability is equivalent to exact
exponent equality after every deletion. -/
theorem stableCentre_iff_all_delete_equal
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ}
    (ht : 0 ≤ t) :
    ConcreteDeletionUnitStable C t ↔
      ∀ (r : V) (hir : i ≠ r)
        (hother :
          Nonempty (OtherVertex (survivingCentre r i hir))),
        centreExponent
            (C.restrictDelete r hir hother) t =
          centreExponent C t := by
  constructor
  · intro hstable r hir hother
    have hmono :=
      centreExponent_mono_restrictDelete
        C hir hother ht
    have hno := hstable r hir hother
    omega
  · intro heq r hir hother
    rw [heq r hir hother]
    omega

#print axioms stableCentre_adjacent_zero_at_split
#print axioms stableCentre_not_bothAdjacentPositive_at_split
#print axioms stableCentre_iff_all_delete_equal

end JSP000404Research
