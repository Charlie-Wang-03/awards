import JSP000404Research.ResidualUnsafeSaturatedWordClassification
import Mathlib.Tactic

/-!
# Rigidity of zero--zero unsafe saturated carriers

If an exact projected-budget vertex has exponent zero, then its projected free
dimension is zero. Hence every retained coordinate is active and its retained
completion cube is a singleton.

For a zero--zero unsafe saturated overlap carrier u<v, the common overlap word
is therefore the unique retained completion word of both endpoints. The two
vertices have exactly the same complete retained n-bit code and differ only in
the residual coordinate of the original n+1-colour canonical code.

Thus the terminal unsafe remainder is not a subcube problem: every such
carrier is exactly one duplicated complete retained code.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem retainedActive_eq_univ_of_exactProjectedBudget_zero
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hsat : ExactProjectedBudget C exponent v)
    (hzero : exponent v = 0) :
    retainedActive C v = (Finset.univ : Finset (Fin n)) := by
  classical
  have hfree : projectedFree C v = 0 := by
    rw [← hsat, hzero]
  unfold projectedFree at hfree
  have hcardLe :
      (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  have hcard :
      (retainedActive C v).card = n := by
    omega
  apply Finset.eq_univ_of_card
  simpa using hcard

theorem retainedCompletionWords_eq_singleton_of_exactProjectedBudget_zero
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hsat : ExactProjectedBudget C exponent v)
    (hzero : exponent v = 0) :
    retainedCompletionWords C v =
      {fun c => retainedBit C v c} := by
  classical
  have hactive :=
    retainedActive_eq_univ_of_exactProjectedBudget_zero
      C exponent hsat hzero
  apply Finset.ext
  intro word
  constructor
  · intro hw
    have hcomp :=
      (mem_retainedCompletionWords C v word).1 hw
    have heq :
        word = fun c => retainedBit C v c := by
      funext c
      exact hcomp c (by rw [hactive]; simp)
    simp [heq]
  · intro hw
    have heq :
        word = fun c => retainedBit C v c := by
      simpa using hw
    subst word
    apply (mem_retainedCompletionWords C v _).2
    intro c hc
    rfl

theorem zero_zero_overlap_sameRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huZero : exponent u = 0)
    (hvZero : exponent v = 0) :
    SameRetained C u v := by
  have huActive :=
    retainedActive_eq_univ_of_exactProjectedBudget_zero
      C exponent huSat huZero
  have hvActive :=
    retainedActive_eq_univ_of_exactProjectedBudget_zero
      C exponent hvSat hvZero
  intro c
  have huComp :=
    (mem_retainedCompletionWords C u word).1 huWord
  have hvComp :=
    (mem_retainedCompletionWords C v word).1 hvWord
  exact
    (huComp c (by rw [huActive]; simp)).symm.trans
      (hvComp c (by rw [hvActive]; simp))

theorem zero_zero_overlap_completion_cubes_eq_singleton
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huZero : exponent u = 0)
    (hvZero : exponent v = 0) :
    retainedCompletionWords C u = {word} ∧
      retainedCompletionWords C v = {word} := by
  have huSingleton :=
    retainedCompletionWords_eq_singleton_of_exactProjectedBudget_zero
      C exponent huSat huZero
  have hvSingleton :=
    retainedCompletionWords_eq_singleton_of_exactProjectedBudget_zero
      C exponent hvSat hvZero
  have huBase :
      (fun c => retainedBit C u c) = word := by
    have hmem : word ∈ {fun c => retainedBit C u c} := by
      rw [← huSingleton]
      exact huWord
    have heq :
        word = (fun c => retainedBit C u c) := by
      simpa using hmem
    exact heq.symm
  have hvBase :
      (fun c => retainedBit C v c) = word := by
    have hmem : word ∈ {fun c => retainedBit C v c} := by
      rw [← hvSingleton]
      exact hvWord
    have heq :
        word = (fun c => retainedBit C v c) := by
      simpa using hmem
    exact heq.symm
  constructor
  · simpa [huBase] using huSingleton
  · simpa [hvBase] using hvSingleton

/-- Terminal unsafe carriers are duplicated complete retained codes. -/
theorem zero_zero_unsafe_saturated_carrier_is_duplicate_full_code
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {word : Fin n → Bool}
    (huv : u < v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huZero : exponent u = 0)
    (hvZero : exponent v = 0) :
    retainedActive C u = (Finset.univ : Finset (Fin n)) ∧
      retainedActive C v = (Finset.univ : Finset (Fin n)) ∧
      SameRetained C u v ∧
      retainedCompletionWords C u = {word} ∧
      retainedCompletionWords C v = {word} := by
  have huActive :=
    retainedActive_eq_univ_of_exactProjectedBudget_zero
      C exponent huSat huZero
  have hvActive :=
    retainedActive_eq_univ_of_exactProjectedBudget_zero
      C exponent hvSat hvZero
  have hsame :=
    zero_zero_overlap_sameRetained
      C exponent huWord hvWord huSat hvSat huZero hvZero
  have hcubes :=
    zero_zero_overlap_completion_cubes_eq_singleton
      C exponent huWord hvWord huSat hvSat huZero hvZero
  exact ⟨huActive, hvActive, hsame, hcubes.1, hcubes.2⟩

#print axioms retainedActive_eq_univ_of_exactProjectedBudget_zero
#print axioms retainedCompletionWords_eq_singleton_of_exactProjectedBudget_zero
#print axioms zero_zero_overlap_sameRetained
#print axioms zero_zero_overlap_completion_cubes_eq_singleton
#print axioms zero_zero_unsafe_saturated_carrier_is_duplicate_full_code

end OrderedEdgeColoring
end JSP000404Research
