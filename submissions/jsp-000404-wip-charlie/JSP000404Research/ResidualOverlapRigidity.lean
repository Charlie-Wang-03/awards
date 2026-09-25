
import JSP000404Research.ResidualUnsafeEdgeBudget
import JSP000404Research.ResidualCompletionAccounting
import Mathlib.Tactic

/-!
# Rigidity of residual edges which actually carry projected overlap

Let u<v and suppose a retained Boolean word lies in both projected completion
cubes Q_u and Q_v.

Then uv is residual.  More importantly, there cannot be a retained colour c
which is incoming at u and outgoing at v.  Such a c is active at both
endpoints, but its canonical retained bit is true at u and false at v, while a
common completion word would have to equal both values.

Hence

  incomingRetained(u) inter outgoingRetained(v) = empty.

For an unsafe residual edge the forbidden list

  incomingRetained(u) union outgoingRetained(v)

is all Fin n.  Combining full union with empty intersection shows that the
retained active sets of u and v already cover every retained coordinate.
Therefore Q_u inter Q_v has no free coordinate and consists of exactly one
Boolean word.

So every unsafe residual edge contributes at most one projected overlap word.
The potentially exponential overlap fibres can occur only on residual edges
which possess at least one safe retained colour.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A common retained completion rules out every through colour. -/
theorem no_throughColour_of_retainedCompletion_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {word : Fin n → Bool}
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v) :
    Disjoint
      (incomingRetained C u)
      (outgoingRetained C v) := by
  classical
  rw [Finset.disjoint_left]
  intro c hInU hOutV
  have huComp :
      RetainedCompletes C u word :=
    (mem_retainedCompletionWords C u word).1 hu
  have hvComp :
      RetainedCompletes C v word :=
    (mem_retainedCompletionWords C v word).1 hv
  have hcActiveU :
      c ∈ retainedActive C u := by
    rw [retainedActive_eq_incoming_union_outgoing C u]
    exact Finset.mem_union_left _ hInU
  have hcActiveV :
      c ∈ retainedActive C v := by
    rw [retainedActive_eq_incoming_union_outgoing C v]
    exact Finset.mem_union_right _ hOutV
  have hbitU :
      retainedBit C u c = true :=
    (mem_incomingRetained_iff_retainedBit_true C u c).1 hInU
  have hnotInV :
      c ∉ incomingRetained C v := by
    exact Finset.disjoint_left.mp
      (incomingRetained_disjoint_outgoingRetained C v)
      hOutV
  have hbitV :
      retainedBit C v c = false := by
    unfold retainedBit
    apply bit_eq_false_iff.mpr
    intro hex
    exact hnotInV
      ((mem_incomingRetained_iff C v c).2 hex)
  have hwU := huComp c hcActiveU
  have hwV := hvComp c hcActiveV
  rw [hbitU] at hwU
  rw [hbitV] at hwV
  rw [hwU] at hwV
  decide

/-- Set form: the through-colour set is empty on every actual overlap pair. -/
theorem residualThroughColours_eq_empty_of_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {word : Fin n → Bool}
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v) :
    residualThroughColours C u v = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c hc
  have hc' :=
    (mem_residualThroughColours C u v c).1 hc
  exact Finset.disjoint_left.mp
    (no_throughColour_of_retainedCompletion_overlap C hu hv)
    hc'.1 hc'.2

/-- On an unsafe overlap pair, the two retained active sets cover all retained
coordinates. -/
theorem retainedActive_union_eq_univ_of_unsafe_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {word : Fin n → Bool}
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    retainedActive C u ∪ retainedActive C v =
      (Finset.univ : Finset (Fin n)) := by
  classical
  have hforbid :=
    unsafe_residual_union_eq_univ C hunsafe
  apply Finset.eq_univ_of_forall
  intro c
  have hcForbid :
      c ∈ incomingRetained C u ∪ outgoingRetained C v := by
    rw [hforbid]
    simp
  rw [Finset.mem_union] at hcForbid
  rw [Finset.mem_union]
  rcases hcForbid with hIn | hOut
  · left
    exact incomingRetained_subset_retainedActive C u hIn
  · right
    exact outgoingRetained_subset_retainedActive C v hOut

/-- There is no common inactive retained coordinate on an unsafe overlap
pair. -/
theorem no_common_inactive_of_unsafe_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {word : Fin n → Bool}
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    ¬ ∃ c : Fin n,
      c ∉ retainedActive C u ∧
      c ∉ retainedActive C v := by
  intro hex
  obtain ⟨c, hcu, hcv⟩ := hex
  have hall :=
    retainedActive_union_eq_univ_of_unsafe_overlap
      C hu hv hunsafe
  have hcUnion :
      c ∈ retainedActive C u ∪ retainedActive C v := by
    rw [hall]
    simp
  rw [Finset.mem_union] at hcUnion
  exact hcUnion.elim hcu hcv

/-- Exact singleton intersection for an unsafe overlap pair. -/
theorem retainedCompletionWords_inter_singleton_of_unsafe_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {word : Fin n → Bool}
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    retainedCompletionWords C u ∩
        retainedCompletionWords C v =
      {word} := by
  classical
  have hno :=
    no_common_inactive_of_unsafe_overlap
      C hu hv hunsafe
  have hSameOnActive :
      ∀ c,
        c ∈ retainedActive C u →
        c ∈ retainedActive C v →
        retainedBit C u c = retainedBit C v c := by
    intro c hcu hcv
    have huComp :=
      (mem_retainedCompletionWords C u word).1 hu
    have hvComp :=
      (mem_retainedCompletionWords C v word).1 hv
    exact (huComp c hcu).symm.trans (hvComp c hcv)
  apply Finset.ext
  intro x
  constructor
  · intro hx
    rw [Finset.mem_inter] at hx
    have hxU :=
      (mem_retainedCompletionWords C u x).1 hx.1
    have hxV :=
      (mem_retainedCompletionWords C v x).1 hx.2
    have hxEq : x = word := by
      funext c
      have hcover :
          c ∈ retainedActive C u ∨
            c ∈ retainedActive C v := by
        by_contra hnot
        push_neg at hnot
        exact hno ⟨c, hnot.1, hnot.2⟩
      rcases hcover with hcu | hcv
      · exact (hxU c hcu).trans
          ((mem_retainedCompletionWords C u word).1 hu c hcu).symm
      · exact (hxV c hcv).trans
          ((mem_retainedCompletionWords C v word).1 hv c hcv).symm
    simp [hxEq]
  · intro hx
    have hxEq : x = word := by simpa using hx
    subst x
    exact Finset.mem_inter.mpr ⟨hu, hv⟩

/-- Cardinal form: an unsafe residual edge which carries overlap contributes
exactly one common completion word. -/
theorem retainedCompletionWords_inter_card_one_of_unsafe_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {word : Fin n → Bool}
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card = 1 := by
  rw [retainedCompletionWords_inter_singleton_of_unsafe_overlap
    C hu hv hunsafe]
  simp

#print axioms no_throughColour_of_retainedCompletion_overlap
#print axioms residualThroughColours_eq_empty_of_overlap
#print axioms retainedActive_union_eq_univ_of_unsafe_overlap
#print axioms retainedCompletionWords_inter_card_one_of_unsafe_overlap

end OrderedEdgeColoring
end JSP000404Research
