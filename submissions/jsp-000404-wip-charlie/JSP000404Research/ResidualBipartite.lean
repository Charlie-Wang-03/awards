import JSP000404Research.ResidualSafeTarget
import Mathlib.Tactic

/-!
# The residual colour class is canonically bipartite

For an ordered-edge colouring by k+1 colours, the last (residual) colour has
no increasing two-edge path.  Hence every residual edge is directed from a
vertex which has an outgoing residual edge to a vertex which has no outgoing
residual edge.

This supplies an explicit Boolean bipartition of the residual colour class.
The result is weaker than an OrderedEdgeColoring recolouring requirement and
matches the even-partition viewpoint of Erdos--Szekeres: the residual class
already carries its own bipartite bit.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Source/sink bit of the residual colour class. -/
noncomputable def residualBit
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1)) (v : V) : Bool :=
  if ∃ w, v < w ∧ IsResidual C v w then true else false

/-- A residual edge always runs from residual-bit true to residual-bit false. -/
theorem residualBit_ne_of_residual
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    {u v : V} (huv : u < v) (hres : IsResidual C u v) :
    residualBit C u ≠ residualBit C v := by
  have hu : ∃ w, u < w ∧ IsResidual C u w :=
    ⟨v, huv, hres⟩
  have hv : ¬ ∃ w, v < w ∧ IsResidual C v w := by
    rintro ⟨w, hvw, hvwRes⟩
    exact no_two_residual_on_path C huv hvw hres hvwRes
  simp [residualBit, hu, hv]

#print axioms residualBit_ne_of_residual

end OrderedEdgeColoring
end JSP000404Research
