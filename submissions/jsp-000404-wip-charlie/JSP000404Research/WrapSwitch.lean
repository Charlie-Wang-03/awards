import JSP000404Research.WrapGraph
import JSP000404Research.CycleParity
import Mathlib.Tactic

/-!
# Local Boolean switch rule for the wrap graph

For an oriented two-edge path x-v-y in a triangle-free wrap graph, compare

* the L/H type of the two wrap edges, encoded by whether each edge is high;
* the ambient-order direction of the two traversed edges, encoded by
  x < v and v < y.

At a non-extremal vertex the order direction is unchanged while the L/H type
flips.  At a local minimum or maximum the order direction flips while the L/H
type stays fixed.  Hence:

  high(xv) = high(vy)  iff  up(xv) != up(vy).

This is exactly the switch rule used by CycleParity.
-/

namespace JSP000404Research
namespace DirectionData

noncomputable def edgeHighBool
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) (u v : V) : Bool :=
  by classical exact decide (EdgeHigh D n u v)

noncomputable def edgeUpBool
    {V : Type*} [LinearOrder V] (u v : V) : Bool :=
  decide (u < v)

theorem edgeLow_not_high
    {V : Type*} [LinearOrder V] {width : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hn : 1 ≤ n) {u v : V}
    (hlow : EdgeLow D u v) :
    ¬EdgeHigh D n u v := by
  unfold EdgeLow EdgeHigh at *
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem edgeHigh_not_low
    {V : Type*} [LinearOrder V] {width : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hn : 1 ≤ n) {u v : V}
    (hhigh : EdgeHigh D n u v) :
    ¬EdgeLow D u v :=
  fun hlow => edgeLow_not_high D hn hlow hhigh

/-- The triangle-free local wrap rule in the exact Boolean form needed for the
cycle parity argument. -/
theorem triangleFree_switch_at_vertex
    {V : Type*} [LinearOrder V] {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n)
    {x v y : V}
    (hxv : (wrapGraph D n).Adj x v)
    (hvy : (wrapGraph D n).Adj v y)
    (hxy : x ≠ y) :
    (edgeHighBool D n x v = edgeHighBool D n v y) ↔
      edgeUpBool x v ≠ edgeUpBool v y := by
  classical
  have hxne : x ≠ v := hxv.1
  have hvne : v ≠ y := hvy.1
  -- For unoriented edge labels, normalization of the two orders
  -- is explicit; it is not interchangeable with a directed label.
  have hsym : EdgeHigh D n y v ↔ EdgeHigh D n v y :=
    edgeHigh_symm D hvne.symm
  rcases lt_or_gt_of_ne hxne with hxvlt | hvxlt
  · rcases lt_or_gt_of_ne hvne with hvylt | hyvlt
    · have hop := triangleFree_opposite_at_between
        D hwidth hdelta hxv hvy hxy (Or.inl ⟨hxvlt, hvylt⟩)
      rcases hop with h | h
      · have hnx := edgeLow_not_high D hn h.1
        simp [edgeHighBool, edgeUpBool, hxvlt, hvylt, hnx, h.2]
      · have hny := edgeLow_not_high D hn h.2
        simp [edgeHighBool, edgeUpBool, hxvlt, hvylt, h.1, hny]
    · have hsame := triangleFree_same_at_local_max
        D htri hxvlt hyvlt hxy hxv hvy.symm
      have hnotvy : ¬ v < y := not_lt.mpr hyvlt.le
      rcases hsame with h | h
      · have hnx := edgeLow_not_high D hn h.1
        have hny : ¬EdgeHigh D n v y := by
          intro hy
          exact (edgeLow_not_high D hn h.2) (hsym.mpr hy)
        simp [edgeHighBool, edgeUpBool, hxvlt, hnotvy, hnx, hny]
      · have hny : EdgeHigh D n v y := hsym.mp h.2
        simp [edgeHighBool, edgeUpBool, hxvlt, hnotvy, h.1, hny]
  · rcases lt_or_gt_of_ne hvne with hvylt | hyvlt
    · have hsame := triangleFree_same_at_local_min
        D htri hvxlt hvylt hxy hxv.symm hvy
      have hnotxv : ¬ x < v := not_lt.mpr hvxlt.le
      have hsx : EdgeHigh D n v x ↔ EdgeHigh D n x v :=
        edgeHigh_symm D (Ne.symm hxne)
      rcases hsame with h | h
      · have hnx : ¬EdgeHigh D n x v := by
          intro hx
          exact (edgeLow_not_high D hn h.1) (hsx.mpr hx)
        have hny := edgeLow_not_high D hn h.2
        simp [edgeHighBool, edgeUpBool, hnotxv, hvylt, hnx, hny]
      · have hnx : EdgeHigh D n x v := hsx.mp h.1
        simp [edgeHighBool, edgeUpBool, hnotxv, hvylt, hnx, h.2]
    · have hop := triangleFree_opposite_at_between
        D hwidth hdelta hxv hvy hxy (Or.inr ⟨hyvlt, hvxlt⟩)
      have hnotxv : ¬ x < v := not_lt.mpr hvxlt.le
      have hnotvy : ¬ v < y := not_lt.mpr hyvlt.le
      rcases hop with h | h
      · have hnx := edgeLow_not_high D hn h.1
        simp [edgeHighBool, edgeUpBool, hnotxv, hnotvy, hnx, h.2]
      · have hny := edgeLow_not_high D hn h.2
        simp [edgeHighBool, edgeUpBool, hnotxv, hnotvy, h.1, hny]

#print axioms edgeLow_not_high
#print axioms triangleFree_switch_at_vertex

end DirectionData
end JSP000404Research
