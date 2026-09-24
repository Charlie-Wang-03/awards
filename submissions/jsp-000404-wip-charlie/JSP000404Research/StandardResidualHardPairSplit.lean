
import JSP000404Research.StandardResidualOuterSplit
import Mathlib.Tactic

/-!
# Interior binary split induced by a hard standard residual pair

For a standard residual edge u<v every interior vertex x satisfies exactly one
of

  residual(u,x), residual(x,v).

This file packages the XOR as an actual finite partition of the open interval
(u,v).  The partition is also exactly the canonical residual-bit split:

  residual(u,x)  iff residualBitCoordinate(x)=true,
  residual(x,v)  iff residualBitCoordinate(x)=false.

When u,v are a hard same-retained pair, every interior x is retained-separated
from both endpoints.  Thus a hard pair behaves as a genuine binary separator
on its interior vertex set even though the two endpoints collide after
dropping the residual coordinate.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

noncomputable def openIntervalVertices
    {V : Type*} [LinearOrder V] [Fintype V]
    (u v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun x => u < x ∧ x < v

@[simp] theorem mem_openIntervalVertices
    {V : Type*} [LinearOrder V] [Fintype V]
    (u v x : V) :
    x ∈ openIntervalVertices u v ↔ u < x ∧ x < v := by
  classical
  simp [openIntervalVertices]

noncomputable def leftResidualInterior
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hwidth : width < (n + 1 : ℕ))
    (u v : V) : Finset V := by
  classical
  let C := standardResidualColoring D n hwidth
  exact (openIntervalVertices u v).filter fun x =>
    IsResidual C u x

noncomputable def rightResidualInterior
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hwidth : width < (n + 1 : ℕ))
    (u v : V) : Finset V := by
  classical
  let C := standardResidualColoring D n hwidth
  exact (openIntervalVertices u v).filter fun x =>
    IsResidual C x v

@[simp] theorem mem_leftResidualInterior
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hwidth : width < (n + 1 : ℕ))
    (u v x : V) :
    x ∈ leftResidualInterior D n hwidth u v ↔
      u < x ∧ x < v ∧
      IsResidual (standardResidualColoring D n hwidth) u x := by
  classical
  simp [leftResidualInterior, openIntervalVertices]

@[simp] theorem mem_rightResidualInterior
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hwidth : width < (n + 1 : ℕ))
    (u v x : V) :
    x ∈ rightResidualInterior D n hwidth u v ↔
      u < x ∧ x < v ∧
      IsResidual (standardResidualColoring D n hwidth) x v := by
  classical
  simp [rightResidualInterior, openIntervalVertices]

/-- The two residual-interior sides are disjoint. -/
theorem residualInterior_disjoint
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hwidth : width < (n + 1 : ℕ))
    (u v : V) :
    Disjoint
      (leftResidualInterior D n hwidth u v)
      (rightResidualInterior D n hwidth u v) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxL hxR
  have hL :=
    (mem_leftResidualInterior D n hwidth u v x).1 hxL
  have hR :=
    (mem_rightResidualInterior D n hwidth u v x).1 hxR
  exact
    (standardResidual_inner_not_both
      D n hwidth hL.1 hL.2.1)
      ⟨hL.2.2, hR.2.2⟩

/-- If the outer edge is residual, the two sides cover every interior vertex. -/
theorem residualInterior_union_eq_openInterval
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hwidth : width < (n + 1 : ℕ))
    {u v : V}
    (huv : u < v)
    (hres :
      IsResidual (standardResidualColoring D n hwidth) u v) :
    leftResidualInterior D n hwidth u v ∪
      rightResidualInterior D n hwidth u v =
        openIntervalVertices u v := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    rw [Finset.mem_union] at hx
    rcases hx with hxL | hxR
    · exact (mem_openIntervalVertices u v x).2
        ⟨(mem_leftResidualInterior D n hwidth u v x).1 hxL |>.1,
         (mem_leftResidualInterior D n hwidth u v x).1 hxL |>.2.1⟩
    · exact (mem_openIntervalVertices u v x).2
        ⟨(mem_rightResidualInterior D n hwidth u v x).1 hxR |>.1,
         (mem_rightResidualInterior D n hwidth u v x).1 hxR |>.2.1⟩
  · intro hx
    have hmid := (mem_openIntervalVertices u v x).1 hx
    rcases standardResidual_inner_at_least_one
        D n hwidth hmid.1 hmid.2 hres with hL | hR
    · rw [Finset.mem_union]
      left
      exact (mem_leftResidualInterior D n hwidth u v x).2
        ⟨hmid.1, hmid.2, hL⟩
    · rw [Finset.mem_union]
      right
      exact (mem_rightResidualInterior D n hwidth u v x).2
        ⟨hmid.1, hmid.2, hR⟩

/-- Left-residual membership is exactly residual-coordinate bit true. -/
theorem leftResidualInterior_iff_residualBit_true
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hwidth : width < (n + 1 : ℕ))
    {u v x : V}
    (hux : u < x) (hxv : x < v)
    (hres :
      IsResidual (standardResidualColoring D n hwidth) u v) :
    IsResidual (standardResidualColoring D n hwidth) u x ↔
      bit (standardResidualColoring D n hwidth)
        x (residualCoord n) = true := by
  let C := standardResidualColoring D n hwidth
  constructor
  · intro huxRes
    have hcol : C.color u x = residualCoord n := by
      apply Fin.ext
      simpa [C, residualCoord] using residual_val_eq C huxRes
    have hbit := edgeColor_bit_upper_eq_true C hux
    simpa [hcol] using hbit
  · intro hxTrue
    rcases standardResidual_inner_xor
        D n hwidth hux hxv hres with hleft | hright
    · exact hleft.1
    · exfalso
      have hcol : C.color x v = residualCoord n := by
        apply Fin.ext
        simpa [C, residualCoord] using residual_val_eq C hright.2
      have hfalse := edgeColor_bit_lower_eq_false C hxv
      rw [hcol] at hfalse
      rw [hfalse] at hxTrue
      contradiction

/-- Right-residual membership is exactly residual-coordinate bit false. -/
theorem rightResidualInterior_iff_residualBit_false
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hwidth : width < (n + 1 : ℕ))
    {u v x : V}
    (hux : u < x) (hxv : x < v)
    (hres :
      IsResidual (standardResidualColoring D n hwidth) u v) :
    IsResidual (standardResidualColoring D n hwidth) x v ↔
      bit (standardResidualColoring D n hwidth)
        x (residualCoord n) = false := by
  let C := standardResidualColoring D n hwidth
  constructor
  · intro hxvRes
    have hcol : C.color x v = residualCoord n := by
      apply Fin.ext
      simpa [C, residualCoord] using residual_val_eq C hxvRes
    have hbit := edgeColor_bit_lower_eq_false C hxv
    simpa [hcol] using hbit
  · intro hxFalse
    rcases standardResidual_inner_xor
        D n hwidth hux hxv hres with hleft | hright
    · exfalso
      have hcol : C.color u x = residualCoord n := by
        apply Fin.ext
        simpa [C, residualCoord] using residual_val_eq C hleft.1
      have htrue := edgeColor_bit_upper_eq_true C hux
      rw [hcol] at htrue
      rw [htrue] at hxFalse
      contradiction
    · exact hright.2

/-- A hard outer pair separates every interior vertex from both endpoints in
the retained code. -/
theorem hardPair_interior_retainedSeparated
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hn : 0 < n)
    (hwidth : width < (n + 1 : ℕ))
    {u v x : V}
    (hux : u < x) (hxv : x < v)
    (hres :
      IsResidual (standardResidualColoring D n hwidth) u v)
    (hsame :
      SameRetained (standardResidualColoring D n hwidth) u v) :
    RetainedSeparated
        (standardResidualColoring D n hwidth) u x ∧
      RetainedSeparated
        (standardResidualColoring D n hwidth) x v :=
  standardResidual_hardPair_interior_separated_both
    D n hn hwidth hux hxv hres hsame

#print axioms residualInterior_disjoint
#print axioms residualInterior_union_eq_openInterval
#print axioms leftResidualInterior_iff_residualBit_true
#print axioms rightResidualInterior_iff_residualBit_false
#print axioms hardPair_interior_retainedSeparated

end DirectionData
end JSP000404Research
