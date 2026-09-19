import JSP000404Research.WrapSwitch
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic

/-!
# Triangle-free wrap graphs are bipartite

There is a direct colouring argument, shorter than an odd-cycle proof.

For an oriented wrap edge u -> v define its parity bit by comparing

* whether the unoriented edge is in the high wrap component, and
* whether u < v in the ambient linear order.

Reversing an edge flips this parity bit.  The local switch theorem from
WrapSwitch says that along every non-backtracking two-edge path the parity bit
also flips.  For a backtrack it flips simply by edge reversal.

Consequently all outgoing wrap edges from a fixed vertex have the same parity
bit.  Use that common outgoing bit as the vertex colour.  Across an edge the
two endpoint colours are opposite because reversing the edge flips parity.

Thus a triangle-free wrap graph is explicitly Boolean-colourable.
-/

namespace JSP000404Research
namespace DirectionData

noncomputable def edgeParity
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) (u v : V) : Bool :=
  decide (edgeHighBool D n u v = edgeUpBool u v)

theorem edgeHighBool_symm
    {V : Type*} [LinearOrder V] {width : ℝ} {n : ℕ}
    (D : DirectionData V width) {u v : V} (huv : u ≠ v) :
    edgeHighBool D n u v = edgeHighBool D n v u := by
  simp [edgeHighBool, (edgeHigh_symm D huv)]

theorem edgeUpBool_reverse_ne
    {V : Type*} [LinearOrder V]
    {u v : V} (huv : u ≠ v) :
    edgeUpBool u v ≠ edgeUpBool v u := by
  rcases lt_or_gt_of_ne huv with huvlt | hvult
  · simp [edgeUpBool, huvlt, not_lt.mpr huvlt.le]
  · simp [edgeUpBool, hvult, not_lt.mpr hvult.le]

/-- Reversing an oriented wrap edge flips the combined edge parity. -/
theorem edgeParity_reverse_ne
    {V : Type*} [LinearOrder V] {width : ℝ} {n : ℕ}
    (D : DirectionData V width) {u v : V} (huv : u ≠ v) :
    edgeParity D n u v ≠ edgeParity D n v u := by
  have hh := edgeHighBool_symm D (n := n) huv
  have hu := edgeUpBool_reverse_ne (u := u) (v := v) huv
  unfold edgeParity
  cases h₁ : edgeHighBool D n u v <;>
    cases h₂ : edgeHighBool D n v u <;>
    cases u₁ : edgeUpBool u v <;>
    cases u₂ : edgeUpBool v u <;>
    simp_all

/-- Along every two-edge path in a triangle-free wrap graph, including an
immediate backtrack, the oriented edge parity flips. -/
theorem triangleFree_edgeParity_alternates
    {V : Type*} [LinearOrder V] {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n)
    {x v y : V}
    (hxv : (wrapGraph D n).Adj x v)
    (hvy : (wrapGraph D n).Adj v y) :
    edgeParity D n x v ≠ edgeParity D n v y := by
  by_cases hxy : x = y
  · subst y
    exact edgeParity_reverse_ne D hxv.1
  · have hs :=
      triangleFree_switch_at_vertex
        D hwidth hdelta hn htri hxv hvy hxy
    unfold edgeParity
    cases hxH : edgeHighBool D n x v <;>
      cases hyH : edgeHighBool D n v y <;>
      cases hxU : edgeUpBool x v <;>
      cases hyU : edgeUpBool v y <;>
      simp_all

/-- All oriented wrap edges leaving the same vertex have one common parity. -/
theorem edgeParity_outgoing_eq
    {V : Type*} [LinearOrder V] {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n)
    {v x y : V}
    (hvx : (wrapGraph D n).Adj v x)
    (hvy : (wrapGraph D n).Adj v y) :
    edgeParity D n v x = edgeParity D n v y := by
  have hrev :
      edgeParity D n x v ≠ edgeParity D n v x :=
    edgeParity_reverse_ne D hvx.1.symm
  have halt :
      edgeParity D n x v ≠ edgeParity D n v y :=
    triangleFree_edgeParity_alternates
      D hwidth hdelta hn htri hvx.symm hvy
  cases hxv : edgeParity D n x v <;>
    cases hvx' : edgeParity D n v x <;>
    cases hvy' : edgeParity D n v y <;>
    simp_all

/-- The common outgoing parity at a vertex; isolated vertices receive false. -/
noncomputable def wrapVertexColor
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) (v : V) : Bool :=
  if h : ∃ w, (wrapGraph D n).Adj v w then
    edgeParity D n v h.choose
  else
    false

theorem wrapVertexColor_eq_edgeParity
    {V : Type*} [LinearOrder V] {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n)
    {v w : V}
    (hvw : (wrapGraph D n).Adj v w) :
    wrapVertexColor D n v = edgeParity D n v w := by
  unfold wrapVertexColor
  split_ifs with h
  · exact edgeParity_outgoing_eq
      D hwidth hdelta hn htri h.choose_spec hvw
  · exact False.elim (h ⟨w, hvw⟩)

/-- Main wrap-band graph theorem: triangle-free implies an explicit Boolean
vertex colouring. -/
theorem wrapGraph_colorable_of_triangleFree
    {V : Type*} [LinearOrder V] {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n) :
    (wrapGraph D n).Colorable 2 := by
  let c : (wrapGraph D n).Coloring Bool :=
    SimpleGraph.Coloring.mk (wrapVertexColor D n) (by
      intro v w hvw
      rw [wrapVertexColor_eq_edgeParity D hwidth hdelta hn htri hvw]
      rw [wrapVertexColor_eq_edgeParity D hwidth hdelta hn htri hvw.symm]
      exact edgeParity_reverse_ne D hvw.ne)
  simpa using c.colorable

theorem wrapGraph_isBipartite_of_triangleFree
    {V : Type*} [LinearOrder V] {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 1 ≤ n)
    (htri : WrapTriangleFree D n) :
    (wrapGraph D n).IsBipartite :=
  wrapGraph_colorable_of_triangleFree D hwidth hdelta hn htri

#print axioms edgeParity_reverse_ne
#print axioms triangleFree_edgeParity_alternates
#print axioms edgeParity_outgoing_eq
#print axioms wrapVertexColor_eq_edgeParity
#print axioms wrapGraph_colorable_of_triangleFree
#print axioms wrapGraph_isBipartite_of_triangleFree

end DirectionData
end JSP000404Research
