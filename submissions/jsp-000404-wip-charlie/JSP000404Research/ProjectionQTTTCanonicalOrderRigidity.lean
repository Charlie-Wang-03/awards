import JSP000404Research.ProjectionOrderCanonicalOrder
import JSP000404Research.ResidualQTTTOrderRigidity
import JSP000404Research.ProjectionStandardBandBudget
import Mathlib.Tactic

/-!
# Q/T/T/T outer-edge rigidity in canonical planar order

The generic projection order used by the residual colouring is exactly the
canonical lexicographic planar order.  Therefore the abstract Q/T/T/T
same-side outer-edge rigidity can be stated directly in geometric order.

On the lower side of the completion owner s, the edge between translated
owners x<y<s uses the farther owner's coordinate cx.  On the upper side,
s<x<y uses the farther owner's coordinate cy.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_QTT_same_canonical_lower_side_outer_edge_eq_far_owner
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {s x y : ProjectionOrdered V}
    (hxyCan :
      CanonicalPointLt p x.toOriginal y.toOriginal)
    (hysCan :
      CanonicalPointLt p y.toOriginal s.toOriginal)
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hxLoss :
      x ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam)
        (planarCentreExponent hp Cfam))
    (hyLoss :
      y ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam)
        (planarCentreExponent hp Cfam))
    (hcx :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      cx ∈ retainedActive R x)
    (hcy :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      cy ∈ retainedActive R y)
    (hcxy : cx ≠ cy)
    (hsQ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      word ∈ retainedCompletionWords R s)
    (hxT :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      word ∈ translatedCompletionWords R x cx)
    (hyT :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      word ∈ translatedCompletionWords R y cy) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let R :=
      planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
    ∃ hret : (R.color x y).val < n,
      retainedColor R x y hret = cx := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp Cfam

  have hxy : x < y :=
    (canonicalPointLt_iff_projection_lt hp x y).1 hxyCan
  have hys : y < s :=
    (canonicalPointLt_iff_projection_lt hp y s).1 hysCan

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap hn hdelta0 hdelta1 ht hlam Cfam
  have hexp : ∀ q, exponent q ≤ n := by
    intro q
    exact Nat.le_of_lt
      (by simpa [exponent] using hprofile.1 q)
  have hone :
      ∀ q, (active R q).card ≤ n - exponent q + 1 := by
    intro q
    simpa [R,exponent] using hprofile.2 q

  exact QTT_same_left_side_outer_edge_eq_left_owner
    R exponent hexp hone
    hxy hys
    (by simpa [R,exponent] using hxLoss)
    (by simpa [R,exponent] using hyLoss)
    (by simpa [R] using hcx)
    (by simpa [R] using hcy)
    hcxy
    (by simpa [R] using hsQ)
    (by simpa [R] using hxT)
    (by simpa [R] using hyT)

theorem planar_QTT_same_canonical_upper_side_outer_edge_eq_far_owner
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {s x y : ProjectionOrdered V}
    (hsxCan :
      CanonicalPointLt p s.toOriginal x.toOriginal)
    (hxyCan :
      CanonicalPointLt p x.toOriginal y.toOriginal)
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hxLoss :
      x ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam)
        (planarCentreExponent hp Cfam))
    (hyLoss :
      y ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam)
        (planarCentreExponent hp Cfam))
    (hcx :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      cx ∈ retainedActive R x)
    (hcy :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      cy ∈ retainedActive R y)
    (hcxy : cx ≠ cy)
    (hsQ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      word ∈ retainedCompletionWords R s)
    (hxT :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      word ∈ translatedCompletionWords R x cx)
    (hyT :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      word ∈ translatedCompletionWords R y cy) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let R :=
      planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
    ∃ hret : (R.color x y).val < n,
      retainedColor R x y hret = cy := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp Cfam

  have hsx : s < x :=
    (canonicalPointLt_iff_projection_lt hp s x).1 hsxCan
  have hxy : x < y :=
    (canonicalPointLt_iff_projection_lt hp x y).1 hxyCan

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap hn hdelta0 hdelta1 ht hlam Cfam
  have hexp : ∀ q, exponent q ≤ n := by
    intro q
    exact Nat.le_of_lt
      (by simpa [exponent] using hprofile.1 q)
  have hone :
      ∀ q, (active R q).card ≤ n - exponent q + 1 := by
    intro q
    simpa [R,exponent] using hprofile.2 q

  exact QTT_same_right_side_outer_edge_eq_right_owner
    R exponent hexp hone
    hsx hxy
    (by simpa [R,exponent] using hxLoss)
    (by simpa [R,exponent] using hyLoss)
    (by simpa [R] using hcx)
    (by simpa [R] using hcy)
    hcxy
    (by simpa [R] using hsQ)
    (by simpa [R] using hxT)
    (by simpa [R] using hyT)

#print axioms planar_QTT_same_canonical_lower_side_outer_edge_eq_far_owner
#print axioms planar_QTT_same_canonical_upper_side_outer_edge_eq_far_owner

end ProjectionOrdered
end JSP000404Research
