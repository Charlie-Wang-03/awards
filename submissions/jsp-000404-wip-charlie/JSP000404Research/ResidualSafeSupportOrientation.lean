import JSP000404Research.ResidualSafeCommonInactiveRigidity
import Mathlib.Tactic

/-!
# Common-active orientation on a support-unsafe overlap

For a no-active-safe pair u<v which actually carries a common completion word,
the active support behaves exactly like a fully unsafe overlap after deleting
the common-inactive coordinates.

The common retained-active set is

  active(u) ∩ active(v) = outgoing(u) ∪ incoming(v).

Thus every common-active displacement coordinate has one of two shared
orientations:

* outgoing at both endpoints;
* incoming at both endpoints.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem retainedActive_inter_eq_outgoing_union_incoming_of_noActiveSafe_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    retainedActive C u ∩ retainedActive C v =
      outgoingRetained C u ∪ incomingRetained C v := by
  classical
  ext c
  rw [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hcu,hcv⟩
    rw [retainedActive_eq_incoming_union_outgoing C u] at hcu
    rcases Finset.mem_union.mp hcu with hInU | hOutU
    · rw [retainedActive_eq_incoming_union_outgoing C v] at hcv
      rcases Finset.mem_union.mp hcv with hInV | hOutV
      · exact Or.inr hInV
      · exact False.elim
          (Finset.disjoint_left.mp
            (incoming_left_disjoint_outgoing_right_of_overlap
              C huWord hvWord)
            hInU hOutV)
    · exact Or.inl hOutU
  · intro h
    rcases h with hOutU | hInV
    · have hOutV :=
        outgoing_subset_right_of_noActiveSafe_overlap C hno hOutU
      exact ⟨
        outgoingRetained_subset_retainedActive C u hOutU,
        outgoingRetained_subset_retainedActive C v hOutV⟩
    · have hInU :=
        incoming_subset_left_of_noActiveSafe_overlap C hno hInV
      exact ⟨
        incomingRetained_subset_retainedActive C u hInU,
        incomingRetained_subset_retainedActive C v hInV⟩

theorem commonActive_outgoingBoth_or_incomingBoth_of_noActiveSafe_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool} {c : Fin n}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hcU : c ∈ retainedActive C u)
    (hcV : c ∈ retainedActive C v) :
    (c ∈ outgoingRetained C u ∧
      c ∈ outgoingRetained C v)
    ∨
    (c ∈ incomingRetained C u ∧
      c ∈ incomingRetained C v) := by
  have hinter :
      c ∈ retainedActive C u ∩ retainedActive C v :=
    Finset.mem_inter.mpr ⟨hcU,hcV⟩
  have heq :=
    retainedActive_inter_eq_outgoing_union_incoming_of_noActiveSafe_overlap
      C hno huWord hvWord
  rw [heq] at hinter
  rcases Finset.mem_union.mp hinter with hOutU | hInV
  · left
    exact ⟨hOutU,
      outgoing_subset_right_of_noActiveSafe_overlap C hno hOutU⟩
  · right
    exact ⟨
      incoming_subset_left_of_noActiveSafe_overlap C hno hInV,
      hInV⟩

#print axioms retainedActive_inter_eq_outgoing_union_incoming_of_noActiveSafe_overlap
#print axioms commonActive_outgoingBoth_or_incomingBoth_of_noActiveSafe_overlap

end OrderedEdgeColoring
end JSP000404Research
