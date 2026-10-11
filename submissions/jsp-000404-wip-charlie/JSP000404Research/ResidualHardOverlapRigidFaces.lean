import JSP000404Research.ResidualHardFaceGlobalTransport
import JSP000404Research.ResidualSameCodeOrientation
import Mathlib.Tactic

/-!
# Exact characterization of hard overlap faces without outgoing transport

For a same-retained pair a<v the only possible failure of the
whole-face outward/inactive flip mechanism is that EVERY outgoing
retained colour at a is already retained-active at v.

Since the canonical retained words are equal, that condition is
EQUIVALENT to containment of partial completion cubes Q_v ⊆ Q_a.
Consequently the FULL upper cube Q_v is overlapped with a,
not just the canonical word or a proper subface.

This isolates a rigorous "nested rigid upper cube" alternative to the
previously proved global full-face transport. No geometric contradiction
with this rigid alternative is claimed.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A hard pair has an available outward/inactive retained colour. -/
def HasOutgoingHardTransport
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V) : Prop :=
  ∃ c : Fin n,
    c ∈ outgoingRetained C a ∧ c ∉ retainedActive C v

/-- If a same-code pair has no outward/inactive colour,
the retained active set of the lower endpoint is contained
in that of the upper endpoint. -/
theorem hard_no_transport_retainedActive_subset
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V}
    (hsame : SameRetained C a v)
    (hno : ¬ HasOutgoingHardTransport C a v) :
    retainedActive C a ⊆ retainedActive C v := by
  classical
  intro c hc
  rw [retainedActive_eq_incoming_union_outgoing C a] at hc
  rcases Finset.mem_union.mp hc with hIn | hOut
  · have hInV : c ∈ incomingRetained C v := by
      rw [← incomingRetained_eq_of_sameRetained C hsame]
      exact hIn
    rw [retainedActive_eq_incoming_union_outgoing C v]
    exact Finset.mem_union_left _ hInV
  · by_contra hnot
    exact hno ⟨c, hOut, hnot⟩

/-- Rigid hard-pair obstruction:
no outward/inactive transport forces FULL cube containment. -/
theorem hard_no_transport_upper_cube_subset_lower
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V}
    (hsame : SameRetained C a v)
    (hno : ¬ HasOutgoingHardTransport C a v) :
    retainedCompletionWords C v ⊆ retainedCompletionWords C a := by
  intro word hvword
  apply (mem_retainedCompletionWords C a word).2
  intro c hc
  have hcV := hard_no_transport_retainedActive_subset
    C hsame hno hc
  have hbit :=
    (mem_retainedCompletionWords C v word).1 hvword c hcV
  exact hbit.trans (hsame c).symm

/-- The converse is also true: a safe outward/inactive
flip provides a Boolean word in Q_v but outside Q_a. -/
theorem hard_upper_cube_subset_implies_no_transport
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V}
    (hsame : SameRetained C a v)
    (hsub : retainedCompletionWords C v ⊆
      retainedCompletionWords C a) :
    ¬ HasOutgoingHardTransport C a v := by
  rintro ⟨c,hout,hinact⟩
  have hupper := sameRetained_flip_mem_inactive_upper_cube
    C a v c hsame hinact
  have hnotLower := outgoing_flip_exits_lower_completion_cube
    C a c hout
  exact hnotLower (hsub hupper)

/-- Exact equivalence between lack of a safe face transport and
the fully nested upper completion cube Q_v ⊆ Q_a. -/
theorem hard_no_transport_iff_upper_cube_subset_lower
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V}
    (hsame : SameRetained C a v) :
    ¬ HasOutgoingHardTransport C a v ↔
      retainedCompletionWords C v ⊆
        retainedCompletionWords C a := by
  constructor
  · exact hard_no_transport_upper_cube_subset_lower C hsame
  · exact hard_upper_cube_subset_implies_no_transport C hsame

/-- Rigid hard carriers overlap in their ENTIRE upper
retained completion cube, rather than a proper subface. -/
theorem hard_no_transport_inter_eq_upper_cube
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V}
    (hsame : SameRetained C a v)
    (hno : ¬ HasOutgoingHardTransport C a v) :
    retainedCompletionWords C a ∩
      retainedCompletionWords C v =
        retainedCompletionWords C v := by
  exact Finset.inter_eq_right.mpr
    (hard_no_transport_upper_cube_subset_lower C hsame hno)

/-- Rigid overlap mass is therefore EXACTLY the size of the
upper endpoint's projected Boolean cube. -/
theorem hard_no_transport_inter_card_eq_projected_cube
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V}
    (hsame : SameRetained C a v)
    (hno : ¬ HasOutgoingHardTransport C a v) :
    (retainedCompletionWords C a ∩
      retainedCompletionWords C v).card =
      2 ^ projectedFree C v := by
  rw [hard_no_transport_inter_eq_upper_cube C hsame hno]
  exact retainedCompletionWords_card C v

/-- No outward/inactive hard transport implies at least as
much projected FREE capacity at the lower endpoint. -/
theorem hard_no_transport_upper_free_le_lower_free
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V}
    (hsame : SameRetained C a v)
    (hno : ¬ HasOutgoingHardTransport C a v) :
    projectedFree C v ≤ projectedFree C a := by
  classical
  have hsubset := hard_no_transport_retainedActive_subset C hsame hno
  have hcard := Finset.card_le_card hsubset
  unfold projectedFree
  omega

#print axioms hard_no_transport_iff_upper_cube_subset_lower
#print axioms hard_no_transport_inter_card_eq_projected_cube
#print axioms hard_no_transport_upper_free_le_lower_free

end OrderedEdgeColoring
end JSP000404Research
