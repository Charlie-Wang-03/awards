
import JSP000404Research.StandardResidual
import JSP000404Research.ResidualBipartite
import Mathlib.Tactic

/-!
# Interval structure of the standard residual graph

For the standard (n+1)-band colouring of DirectionData, residual means that
the normalized direction lies in the short top band [n,t).

This extra metric meaning is much stronger than the abstract
OrderedEdgeColoring axioms.

If u<x<v and uv is residual, DirectionData.between places D(u,v) between
D(u,x) and D(x,v). Since D(u,v) >= n, at least one child edge is residual.
Both cannot be residual because the residual colour has no increasing
two-edge path. Hence exactly one child edge is residual.

Consequently, inside the interval of one residual edge, the residual graph is
completely determined by the canonical residual source/sink bit. In
particular, for u<a<b<v,

  ab is residual
    iff residualBit(a)=true and residualBit(b)=false.

Thus every residual-edge interval carries a complete bipartite threshold
structure, a property unavailable for arbitrary ordered edge colourings.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- The lower endpoint of a residual edge is a residual source. -/
theorem residualBit_eq_true_of_residual
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u < v)
    (hres : IsResidual C u v) :
    residualBit C u = true := by
  unfold residualBit
  simp [⟨v, huv, hres⟩]

/-- The upper endpoint of a residual edge is a residual sink. -/
theorem residualBit_eq_false_of_residual
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u < v)
    (hres : IsResidual C u v) :
    residualBit C v = false := by
  unfold residualBit
  have hno :
      ¬ ∃ w, v < w ∧ IsResidual C v w := by
    rintro ⟨w, hvw, hvwRes⟩
    exact no_two_residual_on_path
      C huv hvw hres hvwRes
  simp [hno]

/-- A standard residual edge recursively chooses exactly one side at every
intermediate vertex. -/
theorem standardResidual_intermediate_exactly_one
    {V : Type*} [LinearOrder V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hwidth : t < (n + 1 : ℕ))
    {u x v : V}
    (hux : u < x)
    (hxv : x < v)
    (hres :
      IsResidual (standardResidualColoring D n hwidth) u v) :
    (IsResidual (standardResidualColoring D n hwidth) u x ∧
      ¬ IsResidual (standardResidualColoring D n hwidth) x v)
    ∨
    (¬ IsResidual (standardResidualColoring D n hwidth) u x ∧
      IsResidual (standardResidualColoring D n hwidth) x v) := by
  let R := standardResidualColoring D n hwidth
  have huv : u < v := hux.trans hxv
  have hhigh :
      (n : ℝ) ≤ D.value u v :=
    (standardResidual_iff_high D n hwidth huv).1 hres
  have hone :
      IsResidual R u x ∨ IsResidual R x v := by
    rcases D.between hux hxv with hforward | hreverse
    · right
      apply (standardResidual_iff_high D n hwidth hxv).2
      exact hhigh.trans hforward.2
    · left
      apply (standardResidual_iff_high D n hwidth hux).2
      exact hhigh.trans hreverse.2
  rcases hone with huxRes | hxvRes
  · left
    refine ⟨huxRes, ?_⟩
    intro hxvRes
    exact no_two_residual_on_path
      R hux hxv huxRes hxvRes
  · right
    refine ⟨?_, hxvRes⟩
    intro huxRes
    exact no_two_residual_on_path
      R hux hxv huxRes hxvRes

/-- Relative to a containing residual edge u--v, an intermediate vertex is a
sink exactly when the left child u--x is residual. -/
theorem standardResidual_left_child_iff_bit_false
    {V : Type*} [LinearOrder V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hwidth : t < (n + 1 : ℕ))
    {u x v : V}
    (hux : u < x)
    (hxv : x < v)
    (hres :
      IsResidual (standardResidualColoring D n hwidth) u v) :
    IsResidual (standardResidualColoring D n hwidth) u x
      ↔
    residualBit (standardResidualColoring D n hwidth) x = false := by
  let R := standardResidualColoring D n hwidth
  constructor
  · intro huxRes
    exact residualBit_eq_false_of_residual
      R hux huxRes
  · intro hxFalse
    rcases standardResidual_intermediate_exactly_one
        D hwidth hux hxv hres with hleft | hright
    · exact hleft.1
    · have hxTrue :=
        residualBit_eq_true_of_residual
          R hxv hright.2
      simp [hxFalse] at hxTrue

/-- Dually, an intermediate vertex is a source exactly when the right child
x--v is residual. -/
theorem standardResidual_right_child_iff_bit_true
    {V : Type*} [LinearOrder V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hwidth : t < (n + 1 : ℕ))
    {u x v : V}
    (hux : u < x)
    (hxv : x < v)
    (hres :
      IsResidual (standardResidualColoring D n hwidth) u v) :
    IsResidual (standardResidualColoring D n hwidth) x v
      ↔
    residualBit (standardResidualColoring D n hwidth) x = true := by
  let R := standardResidualColoring D n hwidth
  constructor
  · intro hxvRes
    exact residualBit_eq_true_of_residual
      R hxv hxvRes
  · intro hxTrue
    rcases standardResidual_intermediate_exactly_one
        D hwidth hux hxv hres with hleft | hright
    · have hxFalse :=
        residualBit_eq_false_of_residual
          R hux hleft.1
      simp [hxTrue] at hxFalse
    · exact hright.2

/-- Inside one containing residual edge, every source-to-sink ordered pair is
itself residual. -/
theorem standardResidual_inside_iff_source_sink
    {V : Type*} [LinearOrder V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hwidth : t < (n + 1 : ℕ))
    {u a b v : V}
    (hua : u < a)
    (hab : a < b)
    (hbv : b < v)
    (hres :
      IsResidual (standardResidualColoring D n hwidth) u v) :
    IsResidual (standardResidualColoring D n hwidth) a b
      ↔
    (residualBit (standardResidualColoring D n hwidth) a = true ∧
     residualBit (standardResidualColoring D n hwidth) b = false) := by
  let R := standardResidualColoring D n hwidth
  constructor
  · intro habRes
    exact ⟨
      residualBit_eq_true_of_residual R hab habRes,
      residualBit_eq_false_of_residual R hab habRes⟩
  · rintro ⟨haTrue, hbFalse⟩
    have hav : a < v := hab.trans hbv
    have hresAV :
        IsResidual R a v :=
      (standardResidual_right_child_iff_bit_true
        D hwidth hua hav hres).2 haTrue
    exact
      (standardResidual_left_child_iff_bit_false
        D hwidth hab hbv hresAV).2 hbFalse

#print axioms standardResidual_intermediate_exactly_one
#print axioms standardResidual_left_child_iff_bit_false
#print axioms standardResidual_right_child_iff_bit_true
#print axioms standardResidual_inside_iff_source_sink

end DirectionData
end JSP000404Research
