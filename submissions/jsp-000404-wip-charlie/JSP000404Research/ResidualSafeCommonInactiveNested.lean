import JSP000404Research.ResidualSafeCommonInactiveReducedZero
import JSP000404Research.ResidualSafeCommonInactiveRigidity
import JSP000404Research.ResidualOverlapCube
import Mathlib.Tactic

/-!
# Nested completion cubes in the one-sided reduced-zero case

Under NoActiveSafeCoordinate, orientations are nested:

  out(u) ⊆ out(v),   in(v) ⊆ in(u).

If the left reduced exponent is zero, tensor rigidity upgrades the first
inclusion to equality out(u)=out(v). Hence

  retainedActive(v) ⊆ retainedActive(u).

Since the two endpoints share one completion word, every canonical constraint
imposed by v agrees with u on the smaller active set. Therefore

  Q_u ⊆ Q_v.

Dually, right reduced-zero gives Q_v ⊆ Q_u.

Thus a reduced-zero hard overlap block is exactly the narrower endpoint cube,
and its cardinality is the free tensor mass 2^d.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem retainedActive_right_subset_left_of_noActiveSafe_reducedZero_left
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (huZero :
      exponent u = (commonInactiveRetained C u v).card) :
    retainedActive C v ⊆ retainedActive C u := by
  have hOutEq :=
    outgoing_eq_of_noActiveSafe_saturated_reducedZero_left
      C exponent hno huWord hvWord huSat huZero
  have hInSub :=
    incoming_subset_left_of_noActiveSafe_overlap C hno
  intro c hc
  rw [retainedActive_eq_incoming_union_outgoing C v] at hc
  rw [retainedActive_eq_incoming_union_outgoing C u]
  rcases Finset.mem_union.mp hc with hIn | hOut
  · exact Finset.mem_union_left _ (hInSub hIn)
  · exact Finset.mem_union_right _ (by simpa [hOutEq] using hOut)

theorem retainedActive_left_subset_right_of_noActiveSafe_reducedZero_right
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hvSat : ExactProjectedBudget C exponent v)
    (hvZero :
      exponent v = (commonInactiveRetained C u v).card) :
    retainedActive C u ⊆ retainedActive C v := by
  have hInEq :=
    incoming_eq_of_noActiveSafe_saturated_reducedZero_right
      C exponent hno huWord hvWord hvSat hvZero
  have hOutSub :=
    outgoing_subset_right_of_noActiveSafe_overlap C hno
  intro c hc
  rw [retainedActive_eq_incoming_union_outgoing C u] at hc
  rw [retainedActive_eq_incoming_union_outgoing C v]
  rcases Finset.mem_union.mp hc with hIn | hOut
  · exact Finset.mem_union_left _ (by simpa [hInEq] using hIn)
  · exact Finset.mem_union_right _ (hOutSub hOut)

theorem completion_subset_of_noActiveSafe_reducedZero_left
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (huZero :
      exponent u = (commonInactiveRetained C u v).card) :
    retainedCompletionWords C u ⊆
      retainedCompletionWords C v := by
  have hActiveSub :=
    retainedActive_right_subset_left_of_noActiveSafe_reducedZero_left
      C exponent hno huBase hvBase huSat huZero
  intro x hx
  apply (mem_retainedCompletionWords C v x).2
  intro c hcV
  have hcU := hActiveSub hcV
  have hxU :=
    (mem_retainedCompletionWords C u x).1 hx
  have hbaseU :=
    (mem_retainedCompletionWords C u base).1 huBase
  have hbaseV :=
    (mem_retainedCompletionWords C v base).1 hvBase
  have hbit :
      retainedBit C u c = retainedBit C v c :=
    (hbaseU c hcU).symm.trans (hbaseV c hcV)
  exact (hxU c hcU).trans hbit

theorem completion_subset_of_noActiveSafe_reducedZero_right
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (hvSat : ExactProjectedBudget C exponent v)
    (hvZero :
      exponent v = (commonInactiveRetained C u v).card) :
    retainedCompletionWords C v ⊆
      retainedCompletionWords C u := by
  have hActiveSub :=
    retainedActive_left_subset_right_of_noActiveSafe_reducedZero_right
      C exponent hno huBase hvBase hvSat hvZero
  intro x hx
  apply (mem_retainedCompletionWords C u x).2
  intro c hcU
  have hcV := hActiveSub hcU
  have hxV :=
    (mem_retainedCompletionWords C v x).1 hx
  have hbaseU :=
    (mem_retainedCompletionWords C u base).1 huBase
  have hbaseV :=
    (mem_retainedCompletionWords C v base).1 hvBase
  have hbit :
      retainedBit C v c = retainedBit C u c :=
    (hbaseV c hcV).symm.trans (hbaseU c hcU)
  exact (hxV c hcV).trans hbit

theorem overlap_eq_left_completion_of_noActiveSafe_reducedZero_left
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (huZero :
      exponent u = (commonInactiveRetained C u v).card) :
    retainedCompletionWords C u ∩ retainedCompletionWords C v =
      retainedCompletionWords C u := by
  apply Finset.inter_eq_left.mpr
  exact completion_subset_of_noActiveSafe_reducedZero_left
    C exponent hno huBase hvBase huSat huZero

theorem overlap_eq_right_completion_of_noActiveSafe_reducedZero_right
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (hvSat : ExactProjectedBudget C exponent v)
    (hvZero :
      exponent v = (commonInactiveRetained C u v).card) :
    retainedCompletionWords C u ∩ retainedCompletionWords C v =
      retainedCompletionWords C v := by
  apply Finset.inter_eq_right.mpr
  exact completion_subset_of_noActiveSafe_reducedZero_right
    C exponent hno huBase hvBase hvSat hvZero

#print axioms retainedActive_right_subset_left_of_noActiveSafe_reducedZero_left
#print axioms retainedActive_left_subset_right_of_noActiveSafe_reducedZero_right
#print axioms completion_subset_of_noActiveSafe_reducedZero_left
#print axioms completion_subset_of_noActiveSafe_reducedZero_right
#print axioms overlap_eq_left_completion_of_noActiveSafe_reducedZero_left
#print axioms overlap_eq_right_completion_of_noActiveSafe_reducedZero_right

end OrderedEdgeColoring
end JSP000404Research
