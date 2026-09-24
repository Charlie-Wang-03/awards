
import JSP000404Research.GenericProjectionOrder
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Reindex a finite planar configuration by its generic projection

GenericProjectionOrder constructs an explicit real-valued projection

  L(v) = projectionValue p (genericProjectionSlope p) v

which is injective on every finite injective planar configuration.

This file packages the same underlying vertex type in a dedicated wrapper and
pulls back the linear order of R along L using LinearOrder.lift'.

The wrapper avoids changing any ambient LinearOrder instance already carried by
the original type V.  Its order is definitionally the generic projection order.

This is the first half of the remaining Planar -> ForwardAngleLift bridge.
-/

namespace JSP000404Research

def ProjectionOrdered (V : Type*) := V
deriving Fintype

namespace ProjectionOrdered

def ofOriginal {V : Type*} (v : V) : ProjectionOrdered V := v

def toOriginal {V : Type*} (v : ProjectionOrdered V) : V := v

@[simp] theorem toOriginal_ofOriginal
    {V : Type*} (v : V) :
    toOriginal (ofOriginal v) = v := rfl

@[simp] theorem ofOriginal_toOriginal
    {V : Type*} (v : ProjectionOrdered V) :
    ofOriginal (toOriginal v) = v := rfl

theorem toOriginal_injective
    {V : Type*} :
    Function.Injective (@toOriginal V) := by
  intro a b h
  exact h

noncomputable def projectionCoord
    {V : Type*} [Fintype V]
    (p : V → Plane) :
    ProjectionOrdered V → ℝ :=
  fun v =>
    projectionValue p (genericProjectionSlope p) v.toOriginal

theorem projectionCoord_injective
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p) :
    Function.Injective (projectionCoord p) := by
  intro u v h
  apply toOriginal_injective
  exact genericProjectionValue_injective hp h

noncomputable instance instLinearOrder
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p) :
    LinearOrder (ProjectionOrdered V) :=
  LinearOrder.lift'
    (projectionCoord p)
    (projectionCoord_injective hp)

/-- Strict order in the wrapper is exactly strict order of the generic
projection coordinates. -/
theorem lt_iff_projectionCoord_lt
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (u v : ProjectionOrdered V) :
    @LT.lt (ProjectionOrdered V) (instLinearOrder hp) u v
      ↔
    projectionCoord p u < projectionCoord p v := by
  rfl

/-- Hence every increasing wrapper edge has positive generic projection
increment. -/
theorem projection_increment_pos
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {u v : ProjectionOrdered V}
    (huv :
      @LT.lt (ProjectionOrdered V) (instLinearOrder hp) u v) :
    0 <
      (p v.toOriginal 0 - p u.toOriginal 0) +
        genericProjectionSlope p *
          (p v.toOriginal 1 - p u.toOriginal 1) := by
  apply projection_difference_pos_of_value_lt
  exact (lt_iff_projectionCoord_lt hp u v).1 huv

/-- Reindexed point map. -/
def reindexedPoint
    {V : Type*}
    (p : V → Plane) :
    ProjectionOrdered V → Plane :=
  fun v => p v.toOriginal

theorem reindexedPoint_injective
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p) :
    Function.Injective (reindexedPoint p) := by
  intro u v h
  apply toOriginal_injective
  exact hp h

#print axioms projectionCoord_injective
#print axioms instLinearOrder
#print axioms projection_increment_pos
#print axioms reindexedPoint_injective

end ProjectionOrdered
end JSP000404Research
