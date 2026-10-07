import JSP000404Research.ResidualSafeCommonInactiveRigidity
import JSP000404Research.ResidualOverlapRigidity
import JSP000404Research.ResidualExactBudget
import Mathlib.Tactic

/-!
# Tensor reduction of the final safe common-inactive saturated block

Assume u,v carry a common completion word, both are exact projected-budget
saturated, and every safe coordinate is common-inactive.

Write

  d = card(commonInactiveRetained C u v).

The active support is unsafe, while the d common-inactive coordinates form a
free Boolean tensor factor.  Exact set decompositions give

  exponent(u) = d + card(out(v) \ out(u)),
  exponent(v) = d + card(in(u) \ in(v)),

and therefore

  exponent(u) + exponent(v)
    + card(in(v)) + card(out(u))
      = n + d.

After subtracting the common free factor from both endpoint exponents,

  (exponent(u)-d) + (exponent(v)-d)
    + card(in(v)) + card(out(u))
      = n-d.

This is exactly the unsafe saturated orientation identity in the reduced
active-support dimension.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem retainedInactive_left_eq_commonInactive_union_outDiff_of_noActiveSafe
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    retainedInactive C u =
      commonInactiveRetained C u v ∪
        (outgoingRetained C v \ outgoingRetained C u) := by
  classical
  ext c
  rw [mem_retainedInactive, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · intro hInactiveU
    by_cases hInactiveV : c ∉ retainedActive C v
    · exact Or.inl
        ((mem_commonInactiveRetained C u v c).2
          ⟨hInactiveU,hInactiveV⟩)
    · have hcActiveV : c ∈ retainedActive C v := by
        exact Classical.byContradiction
          (fun h => hInactiveV h)
      rw [retainedActive_eq_incoming_union_outgoing C v] at hcActiveV
      rcases Finset.mem_union.mp hcActiveV with hcInV | hcOutV
      · have hcInU :=
          incoming_subset_left_of_noActiveSafe_overlap
            C hno hcInV
        exact False.elim
          (hInactiveU
            (incomingRetained_subset_retainedActive C u hcInU))
      · exact Or.inr ⟨hcOutV, by
          intro hcOutU
          exact hInactiveU
            (outgoingRetained_subset_retainedActive C u hcOutU)⟩
  · intro h
    rcases h with hCommon | hDiff
    · exact
        ((mem_commonInactiveRetained C u v c).1 hCommon).1
    · obtain ⟨hcOutV,hNotOutU⟩ := hDiff
      intro hcActiveU
      rw [retainedActive_eq_incoming_union_outgoing C u] at hcActiveU
      rcases Finset.mem_union.mp hcActiveU with hcInU | hcOutU
      · exact Finset.disjoint_left.mp
          (no_throughColour_of_retainedCompletion_overlap
            C huWord hvWord)
          hcInU hcOutV
      · exact hNotOutU hcOutU

theorem retainedInactive_right_eq_commonInactive_union_inDiff_of_noActiveSafe
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    retainedInactive C v =
      commonInactiveRetained C u v ∪
        (incomingRetained C u \ incomingRetained C v) := by
  classical
  ext c
  rw [mem_retainedInactive, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · intro hInactiveV
    by_cases hInactiveU : c ∉ retainedActive C u
    · exact Or.inl
        ((mem_commonInactiveRetained C u v c).2
          ⟨hInactiveU,hInactiveV⟩)
    · have hcActiveU : c ∈ retainedActive C u := by
        exact Classical.byContradiction
          (fun h => hInactiveU h)
      rw [retainedActive_eq_incoming_union_outgoing C u] at hcActiveU
      rcases Finset.mem_union.mp hcActiveU with hcInU | hcOutU
      · exact Or.inr ⟨hcInU, by
          intro hcInV
          exact hInactiveV
            (incomingRetained_subset_retainedActive C v hcInV)⟩
      · have hcOutV :=
          outgoing_subset_right_of_noActiveSafe_overlap
            C hno hcOutU
        exact False.elim
          (hInactiveV
            (outgoingRetained_subset_retainedActive C v hcOutV))
  · intro h
    rcases h with hCommon | hDiff
    · exact
        ((mem_commonInactiveRetained C u v c).1 hCommon).2
    · obtain ⟨hcInU,hNotInV⟩ := hDiff
      intro hcActiveV
      rw [retainedActive_eq_incoming_union_outgoing C v] at hcActiveV
      rcases Finset.mem_union.mp hcActiveV with hcInV | hcOutV
      · exact hNotInV hcInV
      · exact Finset.disjoint_left.mp
          (no_throughColour_of_retainedCompletion_overlap
            C huWord hvWord)
          hcInU hcOutV

theorem exponent_eq_commonInactive_add_outDiff_of_noActiveSafe_saturated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u) :
    exponent u =
      (commonInactiveRetained C u v).card +
        (outgoingRetained C v \ outgoingRetained C u).card := by
  have heq :=
    retainedInactive_left_eq_commonInactive_union_outDiff_of_noActiveSafe
      C hno huWord hvWord
  have hdisj :
      Disjoint
        (commonInactiveRetained C u v)
        (outgoingRetained C v \ outgoingRetained C u) := by
    rw [Finset.disjoint_left]
    intro c hcCommon hcDiff
    have hcOutV := (Finset.mem_sdiff.mp hcDiff).1
    exact
      ((mem_commonInactiveRetained C u v c).1 hcCommon).2
        (outgoingRetained_subset_retainedActive C v hcOutV)
  rw [huSat]
  unfold projectedFree
  rw [← retainedInactive_card C u, heq,
      Finset.card_union_of_disjoint hdisj]

theorem exponent_eq_commonInactive_add_inDiff_of_noActiveSafe_saturated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hvSat : ExactProjectedBudget C exponent v) :
    exponent v =
      (commonInactiveRetained C u v).card +
        (incomingRetained C u \ incomingRetained C v).card := by
  have heq :=
    retainedInactive_right_eq_commonInactive_union_inDiff_of_noActiveSafe
      C hno huWord hvWord
  have hdisj :
      Disjoint
        (commonInactiveRetained C u v)
        (incomingRetained C u \ incomingRetained C v) := by
    rw [Finset.disjoint_left]
    intro c hcCommon hcDiff
    have hcInU := (Finset.mem_sdiff.mp hcDiff).1
    exact
      ((mem_commonInactiveRetained C u v c).1 hcCommon).1
        (incomingRetained_subset_retainedActive C u hcInU)
  rw [hvSat]
  unfold projectedFree
  rw [← retainedInactive_card C v, heq,
      Finset.card_union_of_disjoint hdisj]

theorem noActiveSafe_saturated_orientation_identity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v) :
    exponent u + exponent v +
        (incomingRetained C v).card +
        (outgoingRetained C u).card
      =
    n + (commonInactiveRetained C u v).card := by
  have hInSub :
      incomingRetained C v ⊆ incomingRetained C u :=
    incoming_subset_left_of_noActiveSafe_overlap C hno
  have hOutSub :
      outgoingRetained C u ⊆ outgoingRetained C v :=
    outgoing_subset_right_of_noActiveSafe_overlap C hno
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
  have hforbidUnion :=
    forbidden_union_commonInactive_eq_univ_of_noActiveSafe C hno
  have hforbidDisj :=
    active_union_disjoint_commonInactive_of_noActiveSafe C hno
  have hpartitionCard :
      (residualForbidden C u v).card +
          (commonInactiveRetained C u v).card = n := by
    have hcard :=
      Finset.card_union_of_disjoint hforbidDisj
    rw [hforbidUnion] at hcard
    simpa using hcard.symm
  have hcrossDisj :
      Disjoint
        (incomingRetained C u)
        (outgoingRetained C v) :=
    no_throughColour_of_retainedCompletion_overlap
      C huWord hvWord
  have hforbidCard :
      (residualForbidden C u v).card =
        (incomingRetained C u).card +
          (outgoingRetained C v).card := by
    unfold residualForbidden
    rw [Finset.card_union_of_disjoint hcrossDisj]
  have huExp :=
    exponent_eq_commonInactive_add_outDiff_of_noActiveSafe_saturated
      C exponent hno huWord hvWord huSat
  have hvExp :=
    exponent_eq_commonInactive_add_inDiff_of_noActiveSafe_saturated
      C exponent hno huWord hvWord hvSat
  rw [hforbidCard] at hpartitionCard
  omega

theorem noActiveSafe_saturated_reduced_orientation_identity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v) :
    let d := (commonInactiveRetained C u v).card
    (exponent u - d) + (exponent v - d) +
        (incomingRetained C v).card +
        (outgoingRetained C u).card
      =
    n - d := by
  dsimp
  have huExp :=
    exponent_eq_commonInactive_add_outDiff_of_noActiveSafe_saturated
      C exponent hno huWord hvWord huSat
  have hvExp :=
    exponent_eq_commonInactive_add_inDiff_of_noActiveSafe_saturated
      C exponent hno huWord hvWord hvSat
  have hid :=
    noActiveSafe_saturated_orientation_identity
      C exponent hno huWord hvWord huSat hvSat
  omega

#print axioms exponent_eq_commonInactive_add_outDiff_of_noActiveSafe_saturated
#print axioms exponent_eq_commonInactive_add_inDiff_of_noActiveSafe_saturated
#print axioms noActiveSafe_saturated_orientation_identity
#print axioms noActiveSafe_saturated_reduced_orientation_identity

end OrderedEdgeColoring
end JSP000404Research
