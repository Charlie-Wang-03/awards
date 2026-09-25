
import JSP000404Research.ResidualUnsafeOverlapBudget
import JSP000404Research.RetainedOrientation
import Mathlib.Tactic

/-!
# Orientation nesting on an unsafe overlapping residual pair

Let u<v have a common retained completion word and suppose the residual edge is
unsafe, so

  incoming(u) union outgoing(v) = Fin n.

Overlap compatibility rules out both crossed orientation intersections:

  incoming(u) inter outgoing(v) = empty,
  outgoing(u) inter incoming(v) = empty.

The first is the through-colour obstruction.  The second is its forward
counterpart: outgoing at u has retained bit false, incoming at v has retained
bit true.

Therefore

  outgoing(u) subset outgoing(v),
  incoming(v) subset incoming(u).

Writing A_x for retainedActive(x), whose incoming/outgoing decomposition is
disjoint, we obtain

  A_u inter A_v = outgoing(u) union incoming(v)

(disjoint union), and hence

  card A_u + card A_v = n + card(A_u inter A_v).

Equivalently, for projectedFree(x)=n-card A_x,

  projectedFree(u)+projectedFree(v)+card(A_u inter A_v)=n.

If both endpoints are projected-saturated, the same exact identity holds with
their Sendov exponents.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A common retained completion also excludes the opposite crossed
orientation: outgoing at u versus incoming at v. -/
theorem outgoing_inter_incoming_eq_empty_of_completion_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    outgoingRetained C u ∩ incomingRetained C v = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c hc
  have hcData := Finset.mem_inter.mp hc
  have huComp :=
    (mem_retainedCompletionWords C u word).1 huWord
  have hvComp :=
    (mem_retainedCompletionWords C v word).1 hvWord
  have hcuActive :
      c ∈ retainedActive C u := by
    rw [retainedActive_eq_incoming_union_outgoing C u]
    exact Finset.mem_union_right _ hcData.1
  have hcvActive :
      c ∈ retainedActive C v := by
    rw [retainedActive_eq_incoming_union_outgoing C v]
    exact Finset.mem_union_left _ hcData.2
  have huFalse :
      retainedBit C u c = false := by
    unfold retainedBit
    apply bit_eq_false_iff.mpr
    intro hin
    have hinc :
        c ∈ incomingRetained C u :=
      (mem_incomingRetained_iff C u c).2 hin
    exact Finset.disjoint_left.mp
      (incomingRetained_disjoint_outgoingRetained C u)
      hinc hcData.1
  have hvTrue :
      retainedBit C v c = true :=
    (mem_incomingRetained_iff_retainedBit_true
      C v c).1 hcData.2
  have hwu := huComp c hcuActive
  have hwv := hvComp c hcvActive
  rw [huFalse] at hwu
  rw [hvTrue] at hwv
  rw [hwu] at hwv
  simp at hwv

/-- Unsafe overlap forces every outgoing colour of u to remain outgoing at v. -/
theorem outgoingRetained_subset_outgoingRetained_of_unsafe_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    outgoingRetained C u ⊆ outgoingRetained C v := by
  intro c hcu
  have huniv :=
    unsafe_residual_union_eq_univ C hunsafe
  have hcAll :
      c ∈ incomingRetained C u ∪ outgoingRetained C v := by
    rw [huniv]
    simp
  rw [Finset.mem_union] at hcAll
  rcases hcAll with hincU | houtV
  · exact False.elim
      (Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C u)
        hincU hcu)
  · exact houtV

/-- Dually, every incoming colour of v is already incoming at u. -/
theorem incomingRetained_subset_incomingRetained_of_unsafe_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    incomingRetained C v ⊆ incomingRetained C u := by
  intro c hcv
  have huniv :=
    unsafe_residual_union_eq_univ C hunsafe
  have hcAll :
      c ∈ incomingRetained C u ∪ outgoingRetained C v := by
    rw [huniv]
    simp
  rw [Finset.mem_union] at hcAll
  rcases hcAll with hincU | houtV
  · exact hincU
  · exact False.elim
      (Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C v)
        hcv houtV)

/-- Exact common-active set on an unsafe overlapping pair. -/
theorem retainedActive_inter_eq_outgoing_union_incoming_of_unsafe_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    retainedActive C u ∩ retainedActive C v =
      outgoingRetained C u ∪ incomingRetained C v := by
  classical
  have houtSub :=
    outgoingRetained_subset_outgoingRetained_of_unsafe_overlap
      C hunsafe huWord hvWord
  have hinSub :=
    incomingRetained_subset_incomingRetained_of_unsafe_overlap
      C hunsafe huWord hvWord
  have hcross :
      outgoingRetained C u ∩ incomingRetained C v = ∅ :=
    outgoing_inter_incoming_eq_empty_of_completion_overlap
      C huWord hvWord
  ext c
  constructor
  · intro hc
    have huAct := (Finset.mem_inter.mp hc).1
    have hvAct := (Finset.mem_inter.mp hc).2
    rw [retainedActive_eq_incoming_union_outgoing C u,
        Finset.mem_union] at huAct
    rw [retainedActive_eq_incoming_union_outgoing C v,
        Finset.mem_union] at hvAct
    rw [Finset.mem_union]
    rcases huAct with huIn | huOut
    · rcases hvAct with hvIn | hvOut
      · exact Or.inr hvIn
      · have hthrough :
          c ∈ residualThroughColours C u v := by
            exact (mem_residualThroughColours C u v c).2
              ⟨huIn, hvOut⟩
        exact False.elim
          (not_mem_throughColours_of_completion_overlap
            C huWord hvWord hthrough)
    · exact Or.inl huOut
  · intro hc
    rw [Finset.mem_union] at hc
    rw [Finset.mem_inter]
    rcases hc with huOut | hvIn
    · constructor
      · rw [retainedActive_eq_incoming_union_outgoing C u]
        exact Finset.mem_union_right _ huOut
      · rw [retainedActive_eq_incoming_union_outgoing C v]
        exact Finset.mem_union_right _ (houtSub huOut)
    · constructor
      · rw [retainedActive_eq_incoming_union_outgoing C u]
        exact Finset.mem_union_left _ (hinSub hvIn)
      · rw [retainedActive_eq_incoming_union_outgoing C v]
        exact Finset.mem_union_left _ hvIn

/-- Exact retained-active cardinal balance. -/
theorem unsafe_overlap_retainedActive_card_balance
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    (retainedActive C u).card +
        (retainedActive C v).card =
      n + (retainedActive C u ∩ retainedActive C v).card := by
  classical
  have hcover :=
    retainedActive_union_eq_univ_of_unsafe C hunsafe
  have hcard :=
    Finset.card_union_add_card_inter
      (retainedActive C u)
      (retainedActive C v)
  rw [hcover] at hcard
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- Exact projected-free balance. -/
theorem unsafe_overlap_projectedFree_balance
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    projectedFree C u + projectedFree C v +
        (retainedActive C u ∩ retainedActive C v).card = n := by
  have hbal :=
    unsafe_overlap_retainedActive_card_balance
      C hunsafe huWord hvWord
  have huLe :
      (retainedActive C u).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C u)
  have hvLe :
      (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  unfold projectedFree
  omega

/-- Both-saturated unsafe overlaps satisfy an exact exponent-plus-common-active
identity. -/
theorem unsafe_overlap_saturated_exponent_balance
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (huSat : ProjectedSaturated C exponent u)
    (hvSat : ProjectedSaturated C exponent v) :
    exponent u + exponent v +
        (retainedActive C u ∩ retainedActive C v).card = n := by
  unfold ProjectedSaturated at huSat hvSat
  rw [huSat, hvSat]
  exact unsafe_overlap_projectedFree_balance
    C hunsafe huWord hvWord

#print axioms outgoing_inter_incoming_eq_empty_of_completion_overlap
#print axioms outgoingRetained_subset_outgoingRetained_of_unsafe_overlap
#print axioms incomingRetained_subset_incomingRetained_of_unsafe_overlap
#print axioms unsafe_overlap_retainedActive_card_balance
#print axioms unsafe_overlap_projectedFree_balance
#print axioms unsafe_overlap_saturated_exponent_balance

end OrderedEdgeColoring
end JSP000404Research
