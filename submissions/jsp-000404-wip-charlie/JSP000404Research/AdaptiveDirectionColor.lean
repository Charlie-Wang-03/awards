import JSP000404Research.OrderedDirections
import JSP000404Research.OrderedEdgeColor
import Mathlib.Tactic

/-!
# Adaptive direction colourings

For the Erdős--Szekeres/Sendov direction method, a colour class need not be one
contiguous unit band.  The only local geometric condition required for an
ordered edge colouring is that two consecutive increasing edges assigned the
same colour would have normalized directions less than one unit apart.

DirectionData.middleSeparated says that consecutive increasing edges are
always at least one unit apart.  Hence any assignment satisfying this
same-colour closeness condition automatically yields an OrderedEdgeColoring,
with all weighted Hansel consequences available downstream.

This is the intended interface for adaptive recolouring of narrow direction
subintervals.
-/

namespace JSP000404Research
namespace DirectionData

structure AdaptiveColoring
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (k : ℕ) where
  color : V → V → Fin k
  sameColor_close : ∀ {a v w : V}, a < v → v < w →
    color a v = color v w →
    |D.value a v - D.value v w| < 1

namespace AdaptiveColoring

/-- The geometric closeness condition immediately forbids monochromatic
increasing two-paths. -/
noncomputable def toOrderedEdgeColoring
    {V : Type*} [LinearOrder V] {width : ℝ} {k : ℕ}
    {D : DirectionData V width}
    (C : AdaptiveColoring D k) :
    OrderedEdgeColoring V k where
  color := C.color
  noMonoTwoPath := by
    intro a v w hav hvw
    intro heq
    have hsmall := C.sameColor_close hav hvw heq
    have hlarge := D.middleSeparated hav hvw
    exact (not_lt_of_ge hlarge) hsmall

/-- Ordinary cardinality outlet. -/
theorem card_le_two_pow
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} {k : ℕ} {D : DirectionData V width}
    (C : AdaptiveColoring D k) :
    Fintype.card V ≤ 2 ^ k :=
  OrderedEdgeColoring.card_le_two_pow C.toOrderedEdgeColoring

/-- Weighted missing-colour outlet. -/
theorem weighted_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} {k : ℕ} {D : DirectionData V width}
    (C : AdaptiveColoring D k) :
    ∑ v, 2 ^ (k -
      (OrderedEdgeColoring.active C.toOrderedEdgeColoring v).card) ≤ 2 ^ k :=
  OrderedEdgeColoring.weighted_capacity C.toOrderedEdgeColoring

/-- Exact weighted defect outlet. -/
theorem defect
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} {k : ℕ} {D : DirectionData V width}
    (C : AdaptiveColoring D k) :
    ∑ v, (2 ^ (k -
      (OrderedEdgeColoring.active C.toOrderedEdgeColoring v).card) - 1) ≤
        2 ^ k - Fintype.card V :=
  OrderedEdgeColoring.defect C.toOrderedEdgeColoring

#print axioms toOrderedEdgeColoring
#print axioms card_le_two_pow
#print axioms weighted_capacity
#print axioms defect

end AdaptiveColoring
end DirectionData
end JSP000404Research
