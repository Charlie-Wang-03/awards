
import JSP000404Research.ResidualSaturatedOverlapDecomposition
import JSP000404Research.ResidualOverlapCube
import JSP000404Research.ResidualUnsafeOverlapOrientation
import Mathlib.Tactic

/-!
# Universal dimension identity for saturated--saturated overlap carriers

Let A_u,A_v be the retained active-coordinate sets of two vertices and let

  d = card(commonRetainedInactive(u,v))
    = n - card(A_u union A_v),

  c = card(A_u inter A_v).

If both endpoints satisfy ExactProjectedBudget, then

  k_u = n-card(A_u),
  k_v = n-card(A_v).

Finite inclusion--exclusion therefore gives the exact identity

  k_u + k_v + c = n + d.

If the two completion cubes overlap, a coordinate cannot be incoming at one
endpoint and outgoing at the other: the canonical retained bits would disagree
on a coordinate fixed by both partial words.

Hence on an overlap carrier the common active coordinates split exactly into

  (incoming(u) inter incoming(v))
    disjoint-union
  (outgoing(u) inter outgoing(v)).

So every saturated--saturated overlap carrier satisfies

  k_u + k_v
    + commonIncoming + commonOutgoing
      = n + overlapDimension.

This simultaneously generalizes the same-retained and unsafe orientation
identities already present in the repository.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def commonRetainedActive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) : Finset (Fin n) :=
  retainedActive C u ∩ retainedActive C v

@[simp] theorem mem_commonRetainedActive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c : Fin n) :
    c ∈ commonRetainedActive C u v ↔
      c ∈ retainedActive C u ∧
      c ∈ retainedActive C v := by
  classical
  simp [commonRetainedActive]

/-- Pure inclusion--exclusion identity for any pair of projected-budget
saturated vertices. -/
theorem saturated_pair_dimension_identity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v) :
    exponent u + exponent v +
        (commonRetainedActive C u v).card
      =
    n + (commonRetainedInactive C u v).card := by
  classical
  have hAu :
      (retainedActive C u).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C u)
  have hAv :
      (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  have hUnion :
      (retainedActive C u ∪ retainedActive C v).card ≤ n := by
    simpa using
      Finset.card_le_univ
        (retainedActive C u ∪ retainedActive C v)
  have hIE :=
    Finset.card_union_add_card_inter
      (retainedActive C u)
      (retainedActive C v)
  have hInactive :=
    commonRetainedInactive_card C u v
  unfold ExactProjectedBudget projectedFree at huSat hvSat
  unfold commonRetainedActive
  omega

/-- On a nonempty completion overlap, cross-orientation common active colours
are impossible. -/
theorem incoming_left_disjoint_outgoing_right_of_completion_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    Disjoint (incomingRetained C u) (outgoingRetained C v) :=
  incoming_left_disjoint_outgoing_right_of_overlap
    C huWord hvWord

theorem outgoing_left_disjoint_incoming_right_of_completion_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    Disjoint (outgoingRetained C u) (incomingRetained C v) := by
  have h :=
    incoming_left_disjoint_outgoing_right_of_overlap
      C hvWord huWord
  exact h.symm

/-- Exact same-orientation decomposition of the common active set. -/
theorem commonRetainedActive_eq_sameOrientation_union_of_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    commonRetainedActive C u v =
      (incomingRetained C u ∩ incomingRetained C v) ∪
      (outgoingRetained C u ∩ outgoingRetained C v) := by
  classical
  ext c
  simp only [mem_commonRetainedActive, Finset.mem_union,
    Finset.mem_inter]
  constructor
  · rintro ⟨huActive, hvActive⟩
    rw [retainedActive_eq_incoming_union_outgoing C u] at huActive
    rw [retainedActive_eq_incoming_union_outgoing C v] at hvActive
    rcases Finset.mem_union.mp huActive with huIn | huOut <;>
      rcases Finset.mem_union.mp hvActive with hvIn | hvOut
    · exact Or.inl ⟨huIn, hvIn⟩
    · exact False.elim
        (Finset.disjoint_left.mp
          (incoming_left_disjoint_outgoing_right_of_completion_overlap
            C huWord hvWord)
          huIn hvOut)
    · exact False.elim
        (Finset.disjoint_left.mp
          (outgoing_left_disjoint_incoming_right_of_completion_overlap
            C huWord hvWord)
          huOut hvIn)
    · exact Or.inr ⟨huOut, hvOut⟩
  · intro h
    rcases h with hIn | hOut
    · constructor
      · rw [retainedActive_eq_incoming_union_outgoing C u]
        exact Finset.mem_union_left _ hIn.1
      · rw [retainedActive_eq_incoming_union_outgoing C v]
        exact Finset.mem_union_left _ hIn.2
    · constructor
      · rw [retainedActive_eq_incoming_union_outgoing C u]
        exact Finset.mem_union_right _ hOut.1
      · rw [retainedActive_eq_incoming_union_outgoing C v]
        exact Finset.mem_union_right _ hOut.2

/-- The two same-orientation pieces are disjoint. -/
theorem commonIncoming_disjoint_commonOutgoing
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    Disjoint
      (incomingRetained C u ∩ incomingRetained C v)
      (outgoingRetained C u ∩ outgoingRetained C v) := by
  classical
  rw [Finset.disjoint_left]
  intro c hcIn hcOut
  exact Finset.disjoint_left.mp
    (incomingRetained_disjoint_outgoingRetained C u)
    (Finset.mem_inter.mp hcIn).1
    (Finset.mem_inter.mp hcOut).1

/-- Universal saturated-overlap orientation identity. -/
theorem saturated_overlap_orientation_dimension_identity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v) :
    exponent u + exponent v +
        (incomingRetained C u ∩ incomingRetained C v).card +
        (outgoingRetained C u ∩ outgoingRetained C v).card
      =
    n + (commonRetainedInactive C u v).card := by
  have hid :=
    saturated_pair_dimension_identity
      C exponent huSat hvSat
  have hset :=
    commonRetainedActive_eq_sameOrientation_union_of_overlap
      C huWord hvWord
  have hdisj :=
    commonIncoming_disjoint_commonOutgoing C u v
  have hcard :
      (commonRetainedActive C u v).card =
        (incomingRetained C u ∩ incomingRetained C v).card +
        (outgoingRetained C u ∩ outgoingRetained C v).card := by
    rw [hset, Finset.card_union_of_disjoint hdisj]
  omega

/-- Positive saturated endpoints fit into the block obtained after paying the
common-active orientation credit. -/
theorem saturated_overlap_pair_dyadic_block
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huPos : 1 ≤ exponent u)
    (hvPos : 1 ≤ exponent v) :
    2 ^ exponent u + 2 ^ exponent v
      ≤
    2 ^ ((n + (commonRetainedInactive C u v).card) -
      (commonRetainedActive C u v).card) := by
  have hid :=
    saturated_pair_dimension_identity
      C exponent huSat hvSat
  have hsum :
      exponent u + exponent v ≤
        (n + (commonRetainedInactive C u v).card) -
          (commonRetainedActive C u v).card := by
    omega
  exact two_pow_add_le_two_pow_of_pos_sum_le
    huPos hvPos hsum

#print axioms saturated_pair_dimension_identity
#print axioms commonRetainedActive_eq_sameOrientation_union_of_overlap
#print axioms saturated_overlap_orientation_dimension_identity
#print axioms saturated_overlap_pair_dyadic_block

end OrderedEdgeColoring
end JSP000404Research
