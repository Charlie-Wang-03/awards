
import JSP000404Research.StandardResidual
import JSP000404Research.ResidualBitMerge
import Mathlib.Tactic

/-!
# A residual outer edge exactly splits every interior vertex

Let C be the standard (n+1)-band colouring of ordered direction data, with the
last colour corresponding to the short residual interval [n,width).

If u<v is residual and u<x<v, direction betweenness says that value(u,v)
lies between value(u,x) and value(x,v).  Since value(u,v)>=n, at least one of
the two inner edges is residual.

They cannot both be residual because C is an OrderedEdgeColoring and hence has
no monochromatic increasing two-edge path.

Therefore every interior x satisfies the exact XOR rule

  IsResidual(u,x) xor IsResidual(x,v).

For a hard pair u<v with the same retained code, the non-residual inner edge
also supplies a retained bit separating x from both endpoints.  Thus the hard
collision u,v does not propagate to either inner residual edge.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- Every interior vertex of a residual outer edge is incident residually to
at least one endpoint. -/
theorem standardResidual_inner_at_least_one
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ)
    (hwidth : width < (n + 1 : ℕ))
    {u x v : V}
    (hux : u < x) (hxv : x < v)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v) :
    IsResidual
        (standardResidualColoring D n hwidth) u x ∨
      IsResidual
        (standardResidualColoring D n hwidth) x v := by
  have huv : u < v := hux.trans hxv
  have htop :
      (n : ℝ) ≤ D.value u v :=
    (standardResidual_iff_high D n hwidth huv).1 hres
  rcases D.between hux hxv with hforward | hreverse
  · right
    apply (standardResidual_iff_high D n hwidth hxv).2
    exact htop.trans hforward.2
  · left
    apply (standardResidual_iff_high D n hwidth hux).2
    exact htop.trans hreverse.2

/-- The two inner edges cannot both be residual. -/
theorem standardResidual_inner_not_both
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ)
    (hwidth : width < (n + 1 : ℕ))
    {u x v : V}
    (hux : u < x) (hxv : x < v) :
    ¬ (
      IsResidual
        (standardResidualColoring D n hwidth) u x ∧
      IsResidual
        (standardResidualColoring D n hwidth) x v) := by
  intro h
  let C := standardResidualColoring D n hwidth
  have hcolUX :
      C.color u x = residualCoord n := by
    apply Fin.ext
    simpa [C, residualCoord] using
      residual_val_eq C h.1
  have hcolXV :
      C.color x v = residualCoord n := by
    apply Fin.ext
    simpa [C, residualCoord] using
      residual_val_eq C h.2
  exact C.noMonoTwoPath hux hxv
    (by rw [hcolUX, hcolXV])

/-- Exact XOR rule for an interior vertex of a residual outer edge. -/
theorem standardResidual_inner_xor
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ)
    (hwidth : width < (n + 1 : ℕ))
    {u x v : V}
    (hux : u < x) (hxv : x < v)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v) :
    (IsResidual
        (standardResidualColoring D n hwidth) u x ∧
      ¬ IsResidual
        (standardResidualColoring D n hwidth) x v)
      ∨
    (¬ IsResidual
        (standardResidualColoring D n hwidth) u x ∧
      IsResidual
        (standardResidualColoring D n hwidth) x v) := by
  have hone :=
    standardResidual_inner_at_least_one
      D n hwidth hux hxv hres
  have hnotboth :=
    standardResidual_inner_not_both
      D n hwidth hux hxv
  rcases hone with hleft | hright
  · exact Or.inl ⟨hleft, fun hright => hnotboth ⟨hleft, hright⟩⟩
  · exact Or.inr ⟨fun hleft => hnotboth ⟨hleft, hright⟩, hright⟩

/-- If u and v have the same retained code, any interior x is retained-bit
separated from each endpoint: the unique non-residual inner edge supplies a
retained separator, and the common endpoint code transfers that separator to
the other endpoint. -/
theorem standardResidual_hardPair_interior_separated_both
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hn : 0 < n)
    (hwidth : width < (n + 1 : ℕ))
    {u x v : V}
    (hux : u < x) (hxv : x < v)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v)
    (hsame :
      SameRetained
        (standardResidualColoring D n hwidth) u v) :
    RetainedSeparated
        (standardResidualColoring D n hwidth) u x ∧
      RetainedSeparated
        (standardResidualColoring D n hwidth) x v := by
  let C := standardResidualColoring D n hwidth
  rcases standardResidual_inner_xor
      D n hwidth hux hxv hres with hleft | hright
  · have hretXV :
        (C.color x v).val < n := by
      exact lt_of_not_ge hleft.2
    let c : Fin n := retainedColor C x v hretXV
    have hsepXV :
        retainedBit C x c ≠ retainedBit C v c :=
      retainedBit_ne_of_retained_edge C hxv hretXV
    have huvBit : retainedBit C u c = retainedBit C v c :=
      hsame c
    constructor
    · refine ⟨c, ?_⟩
      intro heq
      exact hsepXV (heq.symm.trans huvBit)
    · exact ⟨c, hsepXV⟩
  · have hretUX :
        (C.color u x).val < n := by
      exact lt_of_not_ge hright.1
    let c : Fin n := retainedColor C u x hretUX
    have hsepUX :
        retainedBit C u c ≠ retainedBit C x c :=
      retainedBit_ne_of_retained_edge C hux hretUX
    have huvBit : retainedBit C u c = retainedBit C v c :=
      hsame c
    constructor
    · exact ⟨c, hsepUX⟩
    · refine ⟨c, ?_⟩
      intro heq
      exact hsepUX (huvBit.trans heq.symm)

/-- In particular neither inner residual edge can itself be a hard vertical
pair when the outer residual edge is hard. -/
theorem standardResidual_hardPair_inner_not_hard
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (n : ℕ) (hn : 0 < n)
    (hwidth : width < (n + 1 : ℕ))
    {u x v : V}
    (hux : u < x) (hxv : x < v)
    (hres :
      IsResidual
        (standardResidualColoring D n hwidth) u v)
    (hsame :
      SameRetained
        (standardResidualColoring D n hwidth) u v) :
    RetainedSeparated
        (standardResidualColoring D n hwidth) u x ∧
      RetainedSeparated
        (standardResidualColoring D n hwidth) x v :=
  standardResidual_hardPair_interior_separated_both
    D n hn hwidth hux hxv hres hsame

#print axioms standardResidual_inner_at_least_one
#print axioms standardResidual_inner_xor
#print axioms standardResidual_hardPair_interior_separated_both

end DirectionData
end JSP000404Research
