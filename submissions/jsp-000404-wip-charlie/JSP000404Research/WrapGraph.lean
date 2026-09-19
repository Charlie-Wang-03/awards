import JSP000404Research.WrapSymmetric
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Tactic

/-!
# The merged wrap-band graph

For a normalized direction system, the prospective special colour in the
lower branch is the union of the low component [0,1) and the high component
[n,width).  This file packages those edges as a simple graph.

A triangle-free hypothesis immediately forces the chord between the two
neighbours of any two-edge wrap path to lie in the ordinary middle region
[1,n).  Combined with WrapSymmetric, this yields the local same/opposite L/H
rules required by the cycle-parity argument.
-/

namespace JSP000404Research
namespace DirectionData

noncomputable def wrapGraph
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) : SimpleGraph V where
  Adj u v :=
    u ≠ v ∧ (EdgeLow D u v ∨ EdgeHigh D n u v)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with hlow | hhigh
    · exact Or.inl ((edgeLow_symm D h.1).mp hlow)
    · exact Or.inr ((edgeHigh_symm D h.1).mp hhigh)⟩
  loopless := ⟨by
    intro v h
    exact h.1 rfl⟩

theorem wrapGraph_adj
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) {u v : V} :
    (wrapGraph D n).Adj u v ↔
      u ≠ v ∧ (EdgeLow D u v ∨ EdgeHigh D n u v) := Iff.rfl

/-- A convenient triangle-free formulation: every two-edge path with distinct
endpoints has a nonedge chord. -/
def WrapTriangleFree
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) : Prop :=
  ∀ ⦃x v y : V⦄,
    (wrapGraph D n).Adj x v →
    (wrapGraph D n).Adj v y →
    x ≠ y →
    ¬(wrapGraph D n).Adj x y

/-- For distinct endpoints, a non-wrap edge lies in the middle interval. -/
theorem edgeMiddle_of_not_wrap
    {V : Type*} [LinearOrder V] {width : ℝ} {n : ℕ}
    (D : DirectionData V width)
    {u v : V} (huv : u ≠ v)
    (hnot : ¬(wrapGraph D n).Adj u v) :
    EdgeMiddle D n u v := by
  rw [wrapGraph_adj] at hnot
  push_neg at hnot
  have hnotWrap := hnot huv
  unfold EdgeMiddle
  constructor
  · exact le_of_not_gt (fun hlow => hnotWrap (Or.inl hlow))
  · exact lt_of_not_ge (fun hhigh => hnotWrap (Or.inr hhigh))

/-- Triangle-free wrap paths have middle chords. -/
theorem middle_chord_of_triangleFree
    {V : Type*} [LinearOrder V] {width : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (htri : WrapTriangleFree D n)
    {x v y : V}
    (hxv : (wrapGraph D n).Adj x v)
    (hvy : (wrapGraph D n).Adj v y)
    (hxy : x ≠ y) :
    EdgeMiddle D n x y :=
  edgeMiddle_of_not_wrap D hxy (htri hxv hvy hxy)

/-- At an ambient-order middle point of a triangle-free two-edge wrap path,
the L/H types are opposite. -/
theorem triangleFree_opposite_at_between
    {V : Type*} [LinearOrder V] {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    {x v y : V}
    (hxv : (wrapGraph D n).Adj x v)
    (hvy : (wrapGraph D n).Adj v y)
    (hxy : x ≠ y)
    (hbetween : (x < v ∧ v < y) ∨ (y < v ∧ v < x)) :
    (EdgeLow D x v ∧ EdgeHigh D n v y) ∨
      (EdgeHigh D n x v ∧ EdgeLow D v y) := by
  exact edgeWrap_opposite_at_between D hwidth hdelta
    hxv.1 hvy.1 hxy hbetween hxv.2 hvy.2

/-- At a local minimum of a triangle-free wrap path, the two L/H types agree. -/
theorem triangleFree_same_at_local_min
    {V : Type*} [LinearOrder V] {width : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (htri : WrapTriangleFree D n)
    {v x y : V}
    (hvx : v < x) (hvy : v < y) (hxy : x ≠ y)
    (hvxAdj : (wrapGraph D n).Adj v x)
    (hvyAdj : (wrapGraph D n).Adj v y) :
    (EdgeLow D v x ∧ EdgeLow D v y) ∨
      (EdgeHigh D n v x ∧ EdgeHigh D n v y) := by
  apply edgeWrap_same_at_local_min D hvx hvy hxy hvxAdj.2 hvyAdj.2
  exact middle_chord_of_triangleFree D htri hvxAdj hvyAdj hxy

/-- At a local maximum of a triangle-free wrap path, the two L/H types agree. -/
theorem triangleFree_same_at_local_max
    {V : Type*} [LinearOrder V] {width : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (htri : WrapTriangleFree D n)
    {v x y : V}
    (hxv : x < v) (hyv : y < v) (hxy : x ≠ y)
    (hxvAdj : (wrapGraph D n).Adj x v)
    (hyvAdj : (wrapGraph D n).Adj y v) :
    (EdgeLow D x v ∧ EdgeLow D y v) ∨
      (EdgeHigh D n x v ∧ EdgeHigh D n y v) := by
  apply edgeWrap_same_at_local_max D hxv hyv hxy hxvAdj.2 hyvAdj.2
  exact middle_chord_of_triangleFree D htri
    hxvAdj hyvAdj.symm hxy

#print axioms wrapGraph_adj
#print axioms edgeMiddle_of_not_wrap
#print axioms middle_chord_of_triangleFree
#print axioms triangleFree_opposite_at_between
#print axioms triangleFree_same_at_local_min
#print axioms triangleFree_same_at_local_max

end DirectionData
end JSP000404Research
