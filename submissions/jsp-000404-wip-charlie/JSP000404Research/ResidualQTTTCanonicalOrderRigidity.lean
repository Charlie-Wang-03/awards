import JSP000404Research.ResidualQTTTOrderRigidity
import JSP000404Research.GenericProjectionCanonicalOrder
import Mathlib.Tactic

/-!
# Canonical-order form of Q/T/T order rigidity

The generic projection order used by the residual colouring coincides with
the canonical planar order.  Therefore the Q/T/T outer-edge colour rigidity
can be stated directly in CanonicalPointLt language.

For two translated owners x,y on the same canonical side of the completion
owner s:
* x < y < s forces the outer edge xy to use x's owner coordinate;
* s < x < y forces the outer edge xy to use y's owner coordinate.

This is the bridge needed to combine residual Q/T/T rigidity with the
canonical four-point side table.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem QTT_canonical_left_side_outer_edge_eq_left_owner
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {n : ℕ}
    (C : OrderedEdgeColoring (ProjectionOrdered V) (n + 1))
    (exponent : ProjectionOrdered V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q,
        (OrderedEdgeColoring.active C q).card
          ≤ n - exponent q + 1)
    {s x y : ProjectionOrdered V}
    (hxy :
      CanonicalPointLt p x.toOriginal y.toOriginal)
    (hys :
      CanonicalPointLt p y.toOriginal s.toOriginal)
    (hxLoss :
      x ∈ OrderedEdgeColoring.projectedLossVertices C exponent)
    (hyLoss :
      y ∈ OrderedEdgeColoring.projectedLossVertices C exponent)
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hcx : cx ∈ OrderedEdgeColoring.retainedActive C x)
    (hcy : cy ∈ OrderedEdgeColoring.retainedActive C y)
    (hcxy : cx ≠ cy)
    (hsQ :
      word ∈ OrderedEdgeColoring.retainedCompletionWords C s)
    (hxT :
      word ∈ OrderedEdgeColoring.translatedCompletionWords C x cx)
    (hyT :
      word ∈ OrderedEdgeColoring.translatedCompletionWords C y cy) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    ∃ hret : (C.color x y).val < n,
      OrderedEdgeColoring.retainedColor C x y hret = cx := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hxy' :
      x < y :=
    (canonicalPointLt_iff_projection_lt hp x y).1 hxy
  have hys' :
      y < s :=
    (canonicalPointLt_iff_projection_lt hp y s).1 hys
  exact
    OrderedEdgeColoring.QTT_same_left_side_outer_edge_eq_left_owner
      C exponent hexp honeLoss
      hxy' hys' hxLoss hyLoss
      hcx hcy hcxy hsQ hxT hyT

theorem QTT_canonical_right_side_outer_edge_eq_right_owner
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {n : ℕ}
    (C : OrderedEdgeColoring (ProjectionOrdered V) (n + 1))
    (exponent : ProjectionOrdered V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q,
        (OrderedEdgeColoring.active C q).card
          ≤ n - exponent q + 1)
    {s x y : ProjectionOrdered V}
    (hsx :
      CanonicalPointLt p s.toOriginal x.toOriginal)
    (hxy :
      CanonicalPointLt p x.toOriginal y.toOriginal)
    (hxLoss :
      x ∈ OrderedEdgeColoring.projectedLossVertices C exponent)
    (hyLoss :
      y ∈ OrderedEdgeColoring.projectedLossVertices C exponent)
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hcx : cx ∈ OrderedEdgeColoring.retainedActive C x)
    (hcy : cy ∈ OrderedEdgeColoring.retainedActive C y)
    (hcxy : cx ≠ cy)
    (hsQ :
      word ∈ OrderedEdgeColoring.retainedCompletionWords C s)
    (hxT :
      word ∈ OrderedEdgeColoring.translatedCompletionWords C x cx)
    (hyT :
      word ∈ OrderedEdgeColoring.translatedCompletionWords C y cy) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    ∃ hret : (C.color x y).val < n,
      OrderedEdgeColoring.retainedColor C x y hret = cy := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hsx' :
      s < x :=
    (canonicalPointLt_iff_projection_lt hp s x).1 hsx
  have hxy' :
      x < y :=
    (canonicalPointLt_iff_projection_lt hp x y).1 hxy
  exact
    OrderedEdgeColoring.QTT_same_right_side_outer_edge_eq_right_owner
      C exponent hexp honeLoss
      hsx' hxy' hxLoss hyLoss
      hcx hcy hcxy hsQ hxT hyT

#print axioms QTT_canonical_left_side_outer_edge_eq_left_owner
#print axioms QTT_canonical_right_side_outer_edge_eq_right_owner

end ProjectionOrdered
end JSP000404Research
