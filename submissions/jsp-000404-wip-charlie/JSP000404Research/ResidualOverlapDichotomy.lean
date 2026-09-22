
import JSP000404Research.ResidualUnsafeOverlap
import Mathlib.Tactic

/-!
# Safe versus unsafe projected overlap carriers

Let u<v carry a common retained completion word.

A retained colour c which is safe for the residual edge avoids

  incomingRetained(u) union outgoingRetained(v).

If c were retained-active at both endpoints, safety would force c to be
outgoing at u and incoming at v.  The canonical retained bits would then be
false at u and true at v, contradicting the existence of the common completion
word.

Therefore every safe target colour is inactive at at least one endpoint of an
overlap carrier.

Combining this with ResidualUnsafeOverlap yields an exact structural
dichotomy for every projected overlap carrier:

* unsafe: its two completion cubes meet in exactly one Boolean word;
* safe: there is a safe retained coordinate which is inactive at at least one
  endpoint.

This is the first direct bridge from cross-slice overlap mass to free-coordinate
slack/displacement.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A safe colour on a pair carrying a common completion word cannot be active
at both endpoints. -/
theorem safe_colour_inactive_one_endpoint_of_completion_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    {c : Fin n}
    (hsafe : c ∉ residualForbidden C u v) :
    c ∉ retainedActive C u ∨
      c ∉ retainedActive C v := by
  classical
  by_contra h
  push_neg at h
  have hactiveU : c ∈ retainedActive C u := h.1
  have hactiveV : c ∈ retainedActive C v := h.2
  have hnotInU : c ∉ incomingRetained C u := by
    intro hc
    exact hsafe (Finset.mem_union_left _ hc)
  have hnotOutV : c ∉ outgoingRetained C v := by
    intro hc
    exact hsafe (Finset.mem_union_right _ hc)
  have hOutU : c ∈ outgoingRetained C u := by
    rw [retainedActive_eq_incoming_union_outgoing C u] at hactiveU
    rcases Finset.mem_union.mp hactiveU with hIn | hOut
    · exact False.elim (hnotInU hIn)
    · exact hOut
  have hInV : c ∈ incomingRetained C v := by
    rw [retainedActive_eq_incoming_union_outgoing C v] at hactiveV
    rcases Finset.mem_union.mp hactiveV with hIn | hOut
    · exact hIn
    · exact False.elim (hnotOutV hOut)
  have huFalse :
      retainedBit C u c = false := by
    unfold retainedBit
    apply bit_eq_false_iff.mpr
    intro hex
    exact hnotInU
      ((mem_incomingRetained_iff C u c).2 hex)
  have hvTrue :
      retainedBit C v c = true :=
    (mem_incomingRetained_iff_retainedBit_true
      C v c).1 hInV
  have huComp :=
    (mem_retainedCompletionWords C u word).1 huWord
  have hvComp :=
    (mem_retainedCompletionWords C v word).1 hvWord
  have hwu := huComp c h.1
  have hwv := hvComp c h.2
  rw [huFalse] at hwu
  rw [hvTrue] at hwv
  rw [hwu] at hwv
  simp at hwv

/-- Safe overlap carriers expose a coordinate which can be changed at one
endpoint without violating that endpoint's retained partial word. -/
theorem exists_safe_inactive_coordinate_of_safe_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hsafe :
      ∃ c : Fin n, c ∉ residualForbidden C u v) :
    ∃ c : Fin n,
      c ∉ residualForbidden C u v ∧
      (c ∉ retainedActive C u ∨
       c ∉ retainedActive C v) := by
  obtain ⟨c, hc⟩ := hsafe
  exact ⟨c, hc,
    safe_colour_inactive_one_endpoint_of_completion_overlap
      C huWord hvWord hc⟩

/-- Carrier-level safe/unsafe dichotomy. -/
theorem completion_overlap_safe_or_unsafe_singleton
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    (∃ c : Fin n,
      c ∉ residualForbidden C u v ∧
      (c ∉ retainedActive C u ∨
       c ∉ retainedActive C v))
    ∨
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v = {word}) := by
  classical
  by_cases hsafe :
      ∃ c : Fin n, c ∉ residualForbidden C u v
  · exact Or.inl
      (exists_safe_inactive_coordinate_of_safe_overlap
        C huWord hvWord hsafe)
  · exact Or.inr
      (retainedCompletionWords_inter_eq_singleton_of_unsafe_overlap
        C hsafe huWord hvWord)

/-- Ordered overlap-word specialization using its unique residual carrier. -/
theorem overlapWord_carrier_safe_or_unsafe_singleton
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {word : Fin n → Bool}
    (hoverlap : word ∈ overlapCompletionWords C) :
    ∃ u v : V,
      u < v ∧
      IsResidual C u v ∧
      word ∈ retainedCompletionWords C u ∧
      word ∈ retainedCompletionWords C v ∧
      ((∃ c : Fin n,
          c ∉ residualForbidden C u v ∧
          (c ∉ retainedActive C u ∨
           c ∉ retainedActive C v))
       ∨
       (retainedCompletionWords C u ∩
          retainedCompletionWords C v = {word})) := by
  obtain ⟨u, v, huv, hres, huWord, hvWord, _huniq⟩ :=
    exists_ordered_residual_pair_of_overlapWord C hoverlap
  refine ⟨u, v, huv, hres, huWord, hvWord, ?_⟩
  exact completion_overlap_safe_or_unsafe_singleton
    C huWord hvWord

#print axioms safe_colour_inactive_one_endpoint_of_completion_overlap
#print axioms exists_safe_inactive_coordinate_of_safe_overlap
#print axioms completion_overlap_safe_or_unsafe_singleton
#print axioms overlapWord_carrier_safe_or_unsafe_singleton

end OrderedEdgeColoring
end JSP000404Research
