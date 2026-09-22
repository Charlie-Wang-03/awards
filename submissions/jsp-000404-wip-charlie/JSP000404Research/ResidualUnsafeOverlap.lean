
import JSP000404Research.ResidualUnsafeEdgeBudget
import JSP000404Research.ResidualSliceAccounting
import Mathlib.Tactic

/-!
# Unsafe projected overlaps are single Boolean words

Let u<v be a residual edge whose retained completion cubes overlap.

Any colour in

  residualThroughColours(u,v)
    = incomingRetained(u) inter outgoingRetained(v)

would force opposite retained canonical bits at u and v, so no common
completion word could exist.  Hence every overlap-carrying residual pair has

  residualThroughColours(u,v) = empty.

If the same residual edge is unsafe for canonical recolouring, its forbidden
list

  incomingRetained(u) union outgoingRetained(v)

is the whole retained palette.  This forbidden list is contained in

  retainedActive(u) union retainedActive(v),

so the latter union is also the whole palette.

Therefore every coordinate is specified by at least one endpoint.  Once one
common completion word exists, all common completion words are forced to be
equal to it.  Thus the intersection of the two projected completion cubes is
a singleton.

So a genuinely unsafe cross-slice overlap costs exactly one Boolean word per
residual pair, never an exponential block.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A through colour is incompatible with a common retained completion word. -/
theorem not_mem_throughColours_of_completion_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    {c : Fin n} :
    c ∉ residualThroughColours C u v := by
  intro hc
  have hcData :=
    (mem_residualThroughColours C u v c).1 hc
  have huComp :=
    (mem_retainedCompletionWords C u word).1 huWord
  have hvComp :=
    (mem_retainedCompletionWords C v word).1 hvWord
  have hcuActive :
      c ∈ retainedActive C u :=
    incomingRetained_subset_retainedActive C u hcData.1
  have hcvActive :
      c ∈ retainedActive C v :=
    outgoingRetained_subset_retainedActive C v hcData.2
  have huTrue :
      retainedBit C u c = true :=
    (mem_incomingRetained_iff_retainedBit_true
      C u c).1 hcData.1
  have hvNotIncoming :
      c ∉ incomingRetained C v := by
    intro hinc
    exact Finset.disjoint_left.mp
      (incomingRetained_disjoint_outgoingRetained C v)
      hinc hcData.2
  have hvFalse :
      retainedBit C v c = false := by
    unfold retainedBit
    apply bit_eq_false_iff.mpr
    intro hex
    exact hvNotIncoming
      ((mem_incomingRetained_iff C v c).2 hex)
  have hwu := huComp c hcuActive
  have hwv := hvComp c hcvActive
  rw [huTrue] at hwu
  rw [hvFalse] at hwv
  rw [hwu] at hwv
  simp at hwv

/-- Hence an overlap-carrying pair has no through colours at all. -/
theorem residualThroughColours_eq_empty_of_completion_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    residualThroughColours C u v = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c _
  exact not_mem_throughColours_of_completion_overlap
    C huWord hvWord

/-- Unsafe residual edges cover every retained coordinate by endpoint activity. -/
theorem retainedActive_union_eq_univ_of_unsafe
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
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
      c ∈ incomingRetained C u ∪
        outgoingRetained C v := by
    rw [hforbid]
    simp
  rw [Finset.mem_union] at hcForbid
  rcases hcForbid with hinc | hout
  · apply Finset.mem_union_left
    exact incomingRetained_subset_retainedActive C u hinc
  · apply Finset.mem_union_right
    exact outgoingRetained_subset_retainedActive C v hout

/-- Under full endpoint activity coverage, one common completion determines all
common completions. -/
theorem common_completion_unique_of_active_union_univ
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hcover :
      retainedActive C u ∪ retainedActive C v =
        (Finset.univ : Finset (Fin n)))
    {base word : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v)
    (hwordU : word ∈ retainedCompletionWords C u)
    (hwordV : word ∈ retainedCompletionWords C v) :
    word = base := by
  have hbU :=
    (mem_retainedCompletionWords C u base).1 hbaseU
  have hbV :=
    (mem_retainedCompletionWords C v base).1 hbaseV
  have hwU :=
    (mem_retainedCompletionWords C u word).1 hwordU
  have hwV :=
    (mem_retainedCompletionWords C v word).1 hwordV
  funext c
  have hc :
      c ∈ retainedActive C u ∨
        c ∈ retainedActive C v := by
    have hcUnion :
        c ∈ retainedActive C u ∪ retainedActive C v := by
      rw [hcover]
      simp
    simpa [Finset.mem_union] using hcUnion
  rcases hc with hcu | hcv
  · exact (hwU c hcu).trans (hbU c hcu).symm
  · exact (hwV c hcv).trans (hbV c hcv).symm

/-- An unsafe overlap pair has singleton completion-cube intersection. -/
theorem retainedCompletionWords_inter_eq_singleton_of_unsafe_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v) :
    retainedCompletionWords C u ∩
        retainedCompletionWords C v =
      {base} := by
  classical
  have hcover :=
    retainedActive_union_eq_univ_of_unsafe C hunsafe
  apply Finset.ext
  intro word
  constructor
  · intro hword
    have hparts := Finset.mem_inter.mp hword
    have heq :=
      common_completion_unique_of_active_union_univ
        C hcover hbaseU hbaseV hparts.1 hparts.2
    simpa [heq]
  · intro hword
    have heq : word = base := by
      simpa using hword
    subst word
    exact Finset.mem_inter.mpr ⟨hbaseU, hbaseV⟩

theorem retainedCompletionWords_inter_card_eq_one_of_unsafe_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v) :
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card = 1 := by
  rw [retainedCompletionWords_inter_eq_singleton_of_unsafe_overlap
    C hunsafe hbaseU hbaseV]
  simp

/-- Every unsafe overlap word is the unique overlap of its carrying residual
pair. -/
theorem overlapWord_unique_for_unsafe_carrier
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {word : Fin n → Bool}
    (hoverlap : word ∈ overlapCompletionWords C)
    {u v : V}
    (huv : u < v)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    ∀ other : Fin n → Bool,
      other ∈ retainedCompletionWords C u →
      other ∈ retainedCompletionWords C v →
      other = word := by
  intro other huOther hvOther
  exact common_completion_unique_of_active_union_univ
    C (retainedActive_union_eq_univ_of_unsafe C hunsafe)
    huWord hvWord huOther hvOther

#print axioms residualThroughColours_eq_empty_of_completion_overlap
#print axioms retainedActive_union_eq_univ_of_unsafe
#print axioms retainedCompletionWords_inter_eq_singleton_of_unsafe_overlap
#print axioms overlapWord_unique_for_unsafe_carrier

end OrderedEdgeColoring
end JSP000404Research
