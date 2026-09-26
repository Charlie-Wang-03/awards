
import JSP000404Research.ResidualUnsafeOverlapOrientation
import JSP000404Research.ResidualExactBudget
import JSP000404Research.ResidualLightFibreDyadic
import Mathlib.Tactic

/-!
# Exact Kraft block for an unsafe saturated overlap carrier

Let u<v carry a common retained completion word and suppose the residual edge
is unsafe.

The unsafe overlap orientation gives

  incoming(v) subset incoming(u),
  outgoing(u) subset outgoing(v),

and overlap forces

  incoming(u) inter outgoing(v) = empty.

Unsafe also gives

  incoming(u) union outgoing(v) = Fin n.

Hence the retained palette splits into four disjoint orientation pieces:

  incoming(v),
  incoming(u) \ incoming(v),
  outgoing(u),
  outgoing(v) \ outgoing(u).

If both endpoints are exact projected-budget saturated, the two difference
pieces have cardinalities exactly exponent(v) and exponent(u), respectively.
Therefore

  exponent(u) + exponent(v)
    + card incoming(v) + card outgoing(u)
      = n.

The inner orientation sets incoming(v) and outgoing(u) are the exact fixed
coordinate credit of this carrier.

If both endpoint exponents are positive, the target pair mass fits inside the
corresponding Kraft block of dimension exponent(u)+exponent(v).
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators


/-- On an unsafe overlap, the lower endpoint's inactive retained coordinates
are exactly the outgoing colours gained at the upper endpoint. -/
theorem retainedInactive_left_eq_outgoing_difference_of_unsafe_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    retainedInactive C u =
      outgoingRetained C v \ outgoingRetained C u := by
  classical
  have hunion :=
    unsafe_residual_union_eq_univ C hunsafe
  have hOutSub :=
    outgoingRetained_subset_outgoingRetained_of_unsafe_overlap
      C hunsafe huWord hvWord
  ext c
  rw [mem_retainedInactive, Finset.mem_sdiff]
  constructor
  · intro hInactive
    have hcAll :
        c ∈ incomingRetained C u ∪ outgoingRetained C v := by
      rw [hunion]
      simp
    rw [Finset.mem_union] at hcAll
    rcases hcAll with hInU | hOutV
    · exfalso
      apply hInactive
      rw [retainedActive_eq_incoming_union_outgoing C u]
      exact Finset.mem_union_left _ hInU
    · refine ⟨hOutV, ?_⟩
      intro hOutU
      apply hInactive
      rw [retainedActive_eq_incoming_union_outgoing C u]
      exact Finset.mem_union_right _ hOutU
  · rintro ⟨hOutV, hNotOutU⟩ hActive
    rw [retainedActive_eq_incoming_union_outgoing C u] at hActive
    rw [Finset.mem_union] at hActive
    rcases hActive with hInU | hOutU
    · exact Finset.disjoint_left.mp
        (incoming_left_disjoint_outgoing_right_of_overlap
          C huWord hvWord)
        hInU hOutV
    · exact hNotOutU hOutU

/-- Symmetrically, the upper endpoint's inactive coordinates are exactly the
incoming colours lost from lower to upper. -/
theorem retainedInactive_right_eq_incoming_difference_of_unsafe_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    retainedInactive C v =
      incomingRetained C u \ incomingRetained C v := by
  classical
  have hunion :=
    unsafe_residual_union_eq_univ C hunsafe
  have hInSub :=
    incomingRetained_subset_incomingRetained_of_unsafe_overlap
      C hunsafe huWord hvWord
  ext c
  rw [mem_retainedInactive, Finset.mem_sdiff]
  constructor
  · intro hInactive
    have hcAll :
        c ∈ incomingRetained C u ∪ outgoingRetained C v := by
      rw [hunion]
      simp
    rw [Finset.mem_union] at hcAll
    rcases hcAll with hInU | hOutV
    · refine ⟨hInU, ?_⟩
      intro hInV
      apply hInactive
      rw [retainedActive_eq_incoming_union_outgoing C v]
      exact Finset.mem_union_left _ hInV
    · exfalso
      apply hInactive
      rw [retainedActive_eq_incoming_union_outgoing C v]
      exact Finset.mem_union_right _ hOutV
  · rintro ⟨hInU, hNotInV⟩ hActive
    rw [retainedActive_eq_incoming_union_outgoing C v] at hActive
    rw [Finset.mem_union] at hActive
    rcases hActive with hInV | hOutV
    · exact hNotInV hInV
    · exact Finset.disjoint_left.mp
        (incoming_left_disjoint_outgoing_right_of_overlap
          C huWord hvWord)
        hInU hOutV

/-- Exact lower-endpoint exponent as an outgoing-orientation difference. -/
theorem exponent_eq_outgoing_difference_card_of_unsafe_overlap_saturated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huSat : ExactProjectedBudget C exponent u) :
    exponent u =
      (outgoingRetained C v \ outgoingRetained C u).card := by
  rw [huSat]
  unfold projectedFree
  rw [← retainedInactive_card C u,
      retainedInactive_left_eq_outgoing_difference_of_unsafe_overlap
        C hunsafe huWord hvWord]

/-- Exact upper-endpoint exponent as an incoming-orientation difference. -/
theorem exponent_eq_incoming_difference_card_of_unsafe_overlap_saturated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (hvSat : ExactProjectedBudget C exponent v) :
    exponent v =
      (incomingRetained C u \ incomingRetained C v).card := by
  rw [hvSat]
  unfold projectedFree
  rw [← retainedInactive_card C v,
      retainedInactive_right_eq_incoming_difference_of_unsafe_overlap
        C hunsafe huWord hvWord]

theorem unsafe_saturated_overlap_orientation_identity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v) :
    exponent u + exponent v +
        (incomingRetained C v).card +
        (outgoingRetained C u).card
      =
    n := by
  have hInSub :
      incomingRetained C v ⊆ incomingRetained C u :=
    incomingRetained_subset_left_of_unsafe C hunsafe
  have hOutSub :
      outgoingRetained C u ⊆ outgoingRetained C v :=
    outgoingRetained_subset_right_of_unsafe C hunsafe
  have hInCard :
      (incomingRetained C u \ incomingRetained C v).card +
          (incomingRetained C v).card
        =
      (incomingRetained C u).card :=
    Finset.card_sdiff_add_card_eq_card hInSub
  have hOutCard :
      (outgoingRetained C v \ outgoingRetained C u).card +
          (outgoingRetained C u).card
        =
      (outgoingRetained C v).card :=
    Finset.card_sdiff_add_card_eq_card hOutSub
  have hThrough :
      residualThroughColours C u v = ∅ :=
    residualThroughColours_eq_empty_of_completion_overlap
      C huWord hvWord
  have hPartition :=
    unsafe_residual_card_balance C hunsafe
  rw [hThrough] at hPartition
  simp at hPartition
  have huExp :
      exponent u =
        (outgoingRetained C v \ outgoingRetained C u).card :=
    exponent_eq_outgoing_difference_card_of_unsafe_overlap_saturated
      C exponent huWord hvWord hunsafe huSat
  have hvExp :
      exponent v =
        (incomingRetained C u \ incomingRetained C v).card :=
    exponent_eq_incoming_difference_card_of_unsafe_overlap_saturated
      C exponent huWord hvWord hunsafe hvSat
  omega

/-- Equivalent dimension form. -/
theorem unsafe_saturated_overlap_exponent_sum_eq_remaining_dimension
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v) :
    exponent u + exponent v =
      n -
        ((incomingRetained C v).card +
         (outgoingRetained C u).card) := by
  have h :=
    unsafe_saturated_overlap_orientation_identity
      C exponent huWord hvWord hunsafe huSat hvSat
  omega

/-- Positive saturated endpoints fit inside the orientation block determined
by the fixed inner incoming/outgoing coordinates. -/
theorem unsafe_saturated_overlap_positive_pair_dyadic_capacity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huPos : 1 ≤ exponent u)
    (hvPos : 1 ≤ exponent v) :
    2 ^ exponent u + 2 ^ exponent v
      ≤
    2 ^
      (n -
        ((incomingRetained C v).card +
         (outgoingRetained C u).card)) := by
  have hsum :=
    unsafe_saturated_overlap_exponent_sum_eq_remaining_dimension
      C exponent huWord hvWord hunsafe huSat hvSat
  have hpair :
      2 ^ exponent u + 2 ^ exponent v ≤
        2 ^ (exponent u + exponent v) :=
    two_pow_add_le_two_pow_of_pos_sum_le
      huPos hvPos (le_rfl)
  rw [hsum] at hpair
  exact hpair

#print axioms unsafe_saturated_overlap_orientation_identity
#print axioms unsafe_saturated_overlap_exponent_sum_eq_remaining_dimension
#print axioms unsafe_saturated_overlap_positive_pair_dyadic_capacity

end OrderedEdgeColoring
end JSP000404Research
