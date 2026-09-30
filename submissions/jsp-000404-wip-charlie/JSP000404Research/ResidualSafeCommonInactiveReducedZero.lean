import JSP000404Research.ResidualSafeCommonInactiveTensor
import Mathlib.Tactic

/-!
# Reduced-zero rigidity: duplicated free subcubes

In the no-active-safe saturated block, let

  d = card(commonInactiveRetained C u v).

The exact tensor formulas imply:

* if exponent(u)=d then out(u)=out(v);
* if exponent(v)=d then in(u)=in(v).

If both reduced exponents are zero, both incoming and outgoing retained
palettes agree, hence the full retained-active sets agree.  Since the two
vertices share one completion word, their canonical constraints agree on this
common active set, so the entire completion cubes are equal.

Thus the double reduced-zero terminal is a duplicated d-dimensional Boolean
subcube, generalizing the unsafe zero-zero duplicated-code singleton.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem outgoing_eq_of_noActiveSafe_saturated_reducedZero_left
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
    outgoingRetained C u = outgoingRetained C v := by
  have huExp :=
    exponent_eq_commonInactive_add_outDiff_of_noActiveSafe_saturated
      C exponent hno huWord hvWord huSat
  have hdiff :
      (outgoingRetained C v \ outgoingRetained C u).card = 0 := by
    rw [huZero] at huExp
    omega
  have hsubVU :
      outgoingRetained C v ⊆ outgoingRetained C u := by
    intro c hcV
    by_contra hcU
    have hcDiff :
        c ∈ outgoingRetained C v \ outgoingRetained C u :=
      Finset.mem_sdiff.mpr ⟨hcV,hcU⟩
    have hpos :
        0 < (outgoingRetained C v \ outgoingRetained C u).card :=
      Finset.card_pos.mpr ⟨c,hcDiff⟩
    omega
  have hsubUV :=
    outgoing_subset_right_of_noActiveSafe_overlap C hno
  exact Finset.Subset.antisymm hsubUV hsubVU

theorem incoming_eq_of_noActiveSafe_saturated_reducedZero_right
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
    incomingRetained C u = incomingRetained C v := by
  have hvExp :=
    exponent_eq_commonInactive_add_inDiff_of_noActiveSafe_saturated
      C exponent hno huWord hvWord hvSat
  have hdiff :
      (incomingRetained C u \ incomingRetained C v).card = 0 := by
    rw [hvZero] at hvExp
    omega
  have hsubUV :
      incomingRetained C u ⊆ incomingRetained C v := by
    intro c hcU
    by_contra hcV
    have hcDiff :
        c ∈ incomingRetained C u \ incomingRetained C v :=
      Finset.mem_sdiff.mpr ⟨hcU,hcV⟩
    have hpos :
        0 < (incomingRetained C u \ incomingRetained C v).card :=
      Finset.card_pos.mpr ⟨c,hcDiff⟩
    omega
  have hsubVU :=
    incoming_subset_left_of_noActiveSafe_overlap C hno
  exact Finset.Subset.antisymm hsubUV hsubVU

theorem retainedActive_eq_of_noActiveSafe_saturated_reducedZero_both
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huZero :
      exponent u = (commonInactiveRetained C u v).card)
    (hvZero :
      exponent v = (commonInactiveRetained C u v).card) :
    retainedActive C u = retainedActive C v := by
  have hOut :=
    outgoing_eq_of_noActiveSafe_saturated_reducedZero_left
      C exponent hno huWord hvWord huSat huZero
  have hIn :=
    incoming_eq_of_noActiveSafe_saturated_reducedZero_right
      C exponent hno huWord hvWord hvSat hvZero
  rw [retainedActive_eq_incoming_union_outgoing C u,
      retainedActive_eq_incoming_union_outgoing C v,
      hIn,hOut]

theorem completion_cubes_eq_of_noActiveSafe_saturated_reducedZero_both
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huZero :
      exponent u = (commonInactiveRetained C u v).card)
    (hvZero :
      exponent v = (commonInactiveRetained C u v).card) :
    retainedCompletionWords C u =
      retainedCompletionWords C v := by
  have hActive :=
    retainedActive_eq_of_noActiveSafe_saturated_reducedZero_both
      C exponent hno huBase hvBase huSat hvSat huZero hvZero
  apply Finset.ext
  intro word
  constructor
  · intro huWord
    apply (mem_retainedCompletionWords C v word).2
    intro c hcV
    have hcU : c ∈ retainedActive C u := by
      rw [hActive]
      exact hcV
    have huComp :=
      (mem_retainedCompletionWords C u word).1 huWord
    have huBaseComp :=
      (mem_retainedCompletionWords C u base).1 huBase
    have hvBaseComp :=
      (mem_retainedCompletionWords C v base).1 hvBase
    have hbitEq :
        retainedBit C u c = retainedBit C v c :=
      (huBaseComp c hcU).symm.trans (hvBaseComp c hcV)
    exact (huComp c hcU).trans hbitEq
  · intro hvWord
    apply (mem_retainedCompletionWords C u word).2
    intro c hcU
    have hcV : c ∈ retainedActive C v := by
      rw [← hActive]
      exact hcU
    have hvComp :=
      (mem_retainedCompletionWords C v word).1 hvWord
    have huBaseComp :=
      (mem_retainedCompletionWords C u base).1 huBase
    have hvBaseComp :=
      (mem_retainedCompletionWords C v base).1 hvBase
    have hbitEq :
        retainedBit C v c = retainedBit C u c :=
      (hvBaseComp c hcV).symm.trans (huBaseComp c hcU)
    exact (hvComp c hcV).trans hbitEq

#print axioms outgoing_eq_of_noActiveSafe_saturated_reducedZero_left
#print axioms incoming_eq_of_noActiveSafe_saturated_reducedZero_right
#print axioms retainedActive_eq_of_noActiveSafe_saturated_reducedZero_both
#print axioms completion_cubes_eq_of_noActiveSafe_saturated_reducedZero_both

end OrderedEdgeColoring
end JSP000404Research
