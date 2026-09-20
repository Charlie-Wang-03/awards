import JSP000404Research.ResidualBitMerge
import Mathlib.Tactic

/-!
# Residual merging after independent component flips

The canonical retained bit is not rigid.  For one retained colour, every
connected component of its bipartite colour class may be flipped
independently without destroying properness on old retained edges.

This file packages that extra freedom abstractly.  A `component` label
records which vertices must be flipped together in each retained colour.
A Boolean `flip` value is then chosen for every labelled component.

If old retained edges have equal component labels at their endpoints, and
every residual edge can be assigned a retained colour on which the reoriented
endpoint bits differ, then all `n+1` old colours collapse to an
`n`-coordinate BinaryEdgePartition.  Hence `|V| <= 2^n`.

No graph-connectivity theory is hidden here: supplying genuine connected
component labels is a separate geometric/combinatorial obligation.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Flip the canonical retained bit according to a per-colour component
orientation. -/
noncomputable def reorientedRetainedBit
    {V K : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (component : V → Fin n → K)
    (flip : Fin n → K → Bool) :
    V → Fin n → Bool :=
  fun v c =>
    if flip c (component v c) then
      !(retainedBit C v c)
    else
      retainedBit C v c

/-- Equal component labels make a component flip act identically at the two
endpoints. -/
theorem reoriented_ne_of_same_component
    {V K : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (component : V → Fin n → K)
    (flip : Fin n → K → Bool)
    {u v : V} {c : Fin n}
    (hcomp : component u c = component v c)
    (hbit : retainedBit C u c ≠ retainedBit C v c) :
    reorientedRetainedBit C component flip u c ≠
      reorientedRetainedBit C component flip v c := by
  unfold reorientedRetainedBit
  rw [hcomp]
  cases h : flip c (component v c) <;>
    simp [h, hbit]

/-- Abstract component-flip certificate for eliminating the residual colour. -/
structure ComponentFlipCertificate
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) where
  Component : Type*
  component : V → Fin n → Component
  flip : Fin n → Component → Bool
  target : V → V → Fin n
  retained_same_component :
    ∀ {u v : V} (huv : u < v)
      (hret : (C.color u v).val < n),
      component u (retainedColor C u v hret) =
        component v (retainedColor C u v hret)
  residual_separated :
    ∀ {u v : V}, u < v → IsResidual C u v →
      reorientedRetainedBit C component flip u (target u v) ≠
        reorientedRetainedBit C component flip v (target u v)

namespace ComponentFlipCertificate

/-- A component-flip certificate directly gives an n-coordinate binary edge
partition. -/
noncomputable def toBinaryEdgePartition
    {V : Type*} [LinearOrder V] {n : ℕ}
    {C : OrderedEdgeColoring V (n + 1)}
    (R : ComponentFlipCertificate C) :
    BinaryEdgePartition V n := by
  classical
  refine
    { edgeColor := fun u v =>
        if hret : (C.color u v).val < n then
          retainedColor C u v hret
        else
          R.target u v
      bit := reorientedRetainedBit C R.component R.flip
      proper := ?_ }
  intro u v huv
  by_cases hret : (C.color u v).val < n
  · simp only [dif_pos hret]
    exact reoriented_ne_of_same_component
      C R.component R.flip
      (R.retained_same_component huv hret)
      (retainedBit_ne_of_retained_edge C huv hret)
  · simp only [dif_neg hret]
    exact R.residual_separated huv hret

/-- Ordinary Hansel capacity after component-wise bit reorientation. -/
theorem card_le_two_pow
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    {C : OrderedEdgeColoring V (n + 1)}
    (R : ComponentFlipCertificate C) :
    Fintype.card V ≤ 2 ^ n :=
  BinaryEdgePartition.card_le_two_pow R.toBinaryEdgePartition

#print axioms toBinaryEdgePartition
#print axioms card_le_two_pow

end ComponentFlipCertificate

#print axioms reoriented_ne_of_same_component

end OrderedEdgeColoring
end JSP000404Research
