import JSP000404Research.ResidualLists
import Mathlib.Tactic

/-!
# Incoming/outgoing retained colours are disjoint

For an admissible ordered-edge colouring, a fixed colour cannot occur on both
an incoming and an outgoing edge at the same vertex: those two edges would
form a monochromatic increasing two-path.

Hence the retained active-colour set splits disjointly into incoming and
outgoing retained colours.  This sharpens the residual-recolouring problem.

For a residual edge u<v, any colour in

  outgoingRetained C u ∩ incomingRetained C v

is automatically

* absent from incomingRetained C u,
* absent from outgoingRetained C v,
* already active at both endpoints.

Therefore such a colour is simultaneously safe and absorbed.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- No retained colour can be both incoming and outgoing at one vertex. -/
theorem incomingRetained_disjoint_outgoingRetained
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1)) (v : V) :
    Disjoint (incomingRetained C v) (outgoingRetained C v) := by
  classical
  rw [Finset.disjoint_left]
  intro c hcin hcout
  obtain ⟨a, hav, hca⟩ :=
    (mem_incomingRetained_iff C v c).1 hcin
  obtain ⟨w, hvw, hcw⟩ :=
    (mem_outgoingRetained_iff C v c).1 hcout
  apply C.noMonoTwoPath hav hvw
  rw [hca, hcw]

/-- The retained active set is exactly the union of incoming and outgoing
retained colours. -/
theorem retainedActive_eq_incoming_union_outgoing
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1)) (v : V) :
    retainedActive C v =
      incomingRetained C v ∪ outgoingRetained C v := by
  classical
  ext c
  simp [retainedActive, incomingRetained, outgoingRetained]

/-- Consequently the retained active count is the sum of the two directed
incidence counts. -/
theorem card_retainedActive_eq_add
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1)) (v : V) :
    (retainedActive C v).card =
      (incomingRetained C v).card + (outgoingRetained C v).card := by
  rw [retainedActive_eq_incoming_union_outgoing C v]
  exact Finset.card_union_of_disjoint
    (incomingRetained_disjoint_outgoingRetained C v)

/-- A colour outgoing at the lower endpoint of a residual edge and incoming at
the upper endpoint avoids the exact local forbidden list. -/
theorem common_forward_colour_not_forbidden
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    {u v : V} {c : Fin k}
    (hcu : c ∈ outgoingRetained C u)
    (hcv : c ∈ incomingRetained C v) :
    c ∉ residualForbidden C u v := by
  classical
  intro hforbid
  rw [Finset.mem_union] at hforbid
  rcases hforbid with hincu | houtv
  · exact Finset.disjoint_left.mp
      (incomingRetained_disjoint_outgoingRetained C u)
      hincu hcu
  · exact Finset.disjoint_left.mp
      (incomingRetained_disjoint_outgoingRetained C v)
      hcv houtv

/-- A common forward colour is a safe local target. -/
theorem common_forward_colour_compatible
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    {u v : V} {c : Fin k}
    (hcu : c ∈ outgoingRetained C u)
    (hcv : c ∈ incomingRetained C v) :
    (∀ {a : V} (hau : a < u)
        (haRet : (C.color a u).val < k),
      c ≠ retainedColor C a u haRet) ∧
    (∀ {w : V} (hvw : v < w)
        (hwRet : (C.color v w).val < k),
      c ≠ retainedColor C v w hwRet) :=
  compatible_target_of_not_mem_forbidden C c
    (common_forward_colour_not_forbidden C hcu hcv)

/-- The same colour is already retained-active at both endpoints, so choosing
it consumes no active-colour slack. -/
theorem common_forward_colour_absorbed
    {V : Type*} [LinearOrder V] {k : ℕ}
    (C : OrderedEdgeColoring V (k + 1))
    {u v : V} {c : Fin k}
    (hcu : c ∈ outgoingRetained C u)
    (hcv : c ∈ incomingRetained C v) :
    c ∈ retainedActive C u ∧ c ∈ retainedActive C v := by
  rw [retainedActive_eq_incoming_union_outgoing C u,
      retainedActive_eq_incoming_union_outgoing C v]
  exact ⟨Finset.mem_union_right _ hcu, Finset.mem_union_left _ hcv⟩

#print axioms incomingRetained_disjoint_outgoingRetained
#print axioms retainedActive_eq_incoming_union_outgoing
#print axioms card_retainedActive_eq_add
#print axioms common_forward_colour_not_forbidden
#print axioms common_forward_colour_compatible
#print axioms common_forward_colour_absorbed

end OrderedEdgeColoring
end JSP000404Research
