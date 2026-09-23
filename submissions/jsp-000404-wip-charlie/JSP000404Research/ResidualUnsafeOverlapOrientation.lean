
import JSP000404Research.ResidualUnsafeOverlap
import JSP000404Research.ResidualBlockerDensity
import JSP000404Research.ResidualExactBudget
import Mathlib.Tactic

/-!
# Exact orientation structure of an unsafe projected-overlap carrier

Let u<v carry a common retained completion word and suppose the residual edge
is completely unsafe.

Unsafe means

  incoming(u) union outgoing(v) = all retained colours.

The common completion word forbids every through colour

  incoming(u) inter outgoing(v),

so these two sets are in fact a partition of the retained palette.

The same unsafe partition and the ordinary incoming/outgoing disjointness at
one vertex imply the monotonicity

  incoming(v) subset incoming(u),
  outgoing(u) subset outgoing(v).

Consequently the retained free-coordinate sets have exact orientation forms

  inactive(u) = outgoing(v) \ outgoing(u),
  inactive(v) = incoming(u) \ incoming(v).

Thus if an endpoint is projected-budget saturated, its Sendov exponent is
literally the cardinality of the corresponding orientation difference.  This
is the discrete structure needed for outward displacement of saturated
overlap words.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem incomingRetained_subset_left_of_unsafe
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    incomingRetained C v ⊆ incomingRetained C u := by
  intro c hcInV
  have hunion :=
    unsafe_residual_union_eq_univ C hunsafe
  have hc :
      c ∈ incomingRetained C u ∪ outgoingRetained C v := by
    rw [hunion]
    simp
  rw [Finset.mem_union] at hc
  rcases hc with hcInU | hcOutV
  · exact hcInU
  · exact False.elim
      (Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C v)
        hcInV hcOutV)

theorem outgoingRetained_subset_right_of_unsafe
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    outgoingRetained C u ⊆ outgoingRetained C v := by
  intro c hcOutU
  have hunion :=
    unsafe_residual_union_eq_univ C hunsafe
  have hc :
      c ∈ incomingRetained C u ∪ outgoingRetained C v := by
    rw [hunion]
    simp
  rw [Finset.mem_union] at hc
  rcases hc with hcInU | hcOutV
  · exact False.elim
      (Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C u)
        hcInU hcOutU)
  · exact hcOutV

/-- On an overlap carrier the unsafe forbidden partition is disjoint. -/
theorem incoming_left_disjoint_outgoing_right_of_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    Disjoint (incomingRetained C u) (outgoingRetained C v) := by
  rw [Finset.disjoint_left]
  intro c hIn hOut
  have hc :
      c ∈ residualThroughColours C u v := by
    exact (mem_residualThroughColours C u v c).2
      ⟨hIn, hOut⟩
  have hempty :=
    residualThroughColours_eq_empty_of_completion_overlap
      C huWord hvWord
  rw [hempty] at hc
  simp at hc

/-- Exact free-coordinate set at the lower endpoint. -/
theorem retainedInactive_eq_outgoingRight_sdiff_outgoingLeft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    retainedInactive C u =
      outgoingRetained C v \ outgoingRetained C u := by
  classical
  have hdisj :=
    incoming_left_disjoint_outgoing_right_of_overlap
      C huWord hvWord
  have hunion :=
    unsafe_residual_union_eq_univ C hunsafe
  ext c
  constructor
  · intro hcInactive
    have hcNotActive :
        c ∉ retainedActive C u :=
      (mem_retainedInactive C u c).1 hcInactive
    have hcNotIn : c ∉ incomingRetained C u := by
      intro hc
      apply hcNotActive
      rw [retainedActive_eq_incoming_union_outgoing C u]
      exact Finset.mem_union_left _ hc
    have hcNotOutU : c ∉ outgoingRetained C u := by
      intro hc
      apply hcNotActive
      rw [retainedActive_eq_incoming_union_outgoing C u]
      exact Finset.mem_union_right _ hc
    have hcUnion :
        c ∈ incomingRetained C u ∪ outgoingRetained C v := by
      rw [hunion]
      simp
    rw [Finset.mem_union] at hcUnion
    have hcOutV : c ∈ outgoingRetained C v := by
      rcases hcUnion with hcIn | hcOut
      · exact False.elim (hcNotIn hcIn)
      · exact hcOut
    exact Finset.mem_sdiff.mpr ⟨hcOutV, hcNotOutU⟩
  · intro hc
    have hcData := Finset.mem_sdiff.mp hc
    apply (mem_retainedInactive C u c).2
    rw [retainedActive_eq_incoming_union_outgoing C u]
    intro hcActive
    rw [Finset.mem_union] at hcActive
    rcases hcActive with hcIn | hcOut
    · exact Finset.disjoint_left.mp hdisj hcIn hcData.1
    · exact hcData.2 hcOut

/-- Exact free-coordinate set at the upper endpoint. -/
theorem retainedInactive_eq_incomingLeft_sdiff_incomingRight
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    retainedInactive C v =
      incomingRetained C u \ incomingRetained C v := by
  classical
  have hdisj :=
    incoming_left_disjoint_outgoing_right_of_overlap
      C huWord hvWord
  have hunion :=
    unsafe_residual_union_eq_univ C hunsafe
  ext c
  constructor
  · intro hcInactive
    have hcNotActive :
        c ∉ retainedActive C v :=
      (mem_retainedInactive C v c).1 hcInactive
    have hcNotInV : c ∉ incomingRetained C v := by
      intro hc
      apply hcNotActive
      rw [retainedActive_eq_incoming_union_outgoing C v]
      exact Finset.mem_union_left _ hc
    have hcNotOutV : c ∉ outgoingRetained C v := by
      intro hc
      apply hcNotActive
      rw [retainedActive_eq_incoming_union_outgoing C v]
      exact Finset.mem_union_right _ hc
    have hcUnion :
        c ∈ incomingRetained C u ∪ outgoingRetained C v := by
      rw [hunion]
      simp
    rw [Finset.mem_union] at hcUnion
    have hcInU : c ∈ incomingRetained C u := by
      rcases hcUnion with hcIn | hcOut
      · exact hcIn
      · exact False.elim (hcNotOutV hcOut)
    exact Finset.mem_sdiff.mpr ⟨hcInU, hcNotInV⟩
  · intro hc
    have hcData := Finset.mem_sdiff.mp hc
    apply (mem_retainedInactive C v c).2
    rw [retainedActive_eq_incoming_union_outgoing C v]
    intro hcActive
    rw [Finset.mem_union] at hcActive
    rcases hcActive with hcIn | hcOut
    · exact hcData.2 hcIn
    · exact Finset.disjoint_left.mp hdisj hcData.1 hcOut

theorem projectedFree_eq_outgoing_difference_card_of_unsafe_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    projectedFree C u =
      (outgoingRetained C v \ outgoingRetained C u).card := by
  unfold projectedFree
  rw [← retainedInactive_card C u,
      retainedInactive_eq_outgoingRight_sdiff_outgoingLeft
        C huWord hvWord hunsafe]

theorem projectedFree_eq_incoming_difference_card_of_unsafe_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    projectedFree C v =
      (incomingRetained C u \ incomingRetained C v).card := by
  unfold projectedFree
  rw [← retainedInactive_card C v,
      retainedInactive_eq_incomingLeft_sdiff_incomingRight
        C huWord hvWord hunsafe]

/-- Saturation identifies the lower exponent with the right-going orientation
difference. -/
theorem exponent_eq_outgoing_difference_card_of_unsafe_overlap_saturated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (hsat : ExactProjectedBudget C exponent u) :
    exponent u =
      (outgoingRetained C v \ outgoingRetained C u).card := by
  rw [hsat,
      projectedFree_eq_outgoing_difference_card_of_unsafe_overlap
        C huWord hvWord hunsafe]

/-- Symmetric upper-endpoint form. -/
theorem exponent_eq_incoming_difference_card_of_unsafe_overlap_saturated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (hsat : ExactProjectedBudget C exponent v) :
    exponent v =
      (incomingRetained C u \ incomingRetained C v).card := by
  rw [hsat,
      projectedFree_eq_incoming_difference_card_of_unsafe_overlap
        C huWord hvWord hunsafe]

#print axioms incomingRetained_subset_left_of_unsafe
#print axioms outgoingRetained_subset_right_of_unsafe
#print axioms retainedInactive_eq_outgoingRight_sdiff_outgoingLeft
#print axioms retainedInactive_eq_incomingLeft_sdiff_incomingRight
#print axioms exponent_eq_outgoing_difference_card_of_unsafe_overlap_saturated
#print axioms exponent_eq_incoming_difference_card_of_unsafe_overlap_saturated

end OrderedEdgeColoring
end JSP000404Research
