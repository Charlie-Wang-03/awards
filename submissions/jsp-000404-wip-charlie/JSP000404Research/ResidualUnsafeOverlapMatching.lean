
import JSP000404Research.ResidualUnsafeOverlapOrientation
import Mathlib.Tactic

/-!
# Unsafe projected-overlap residual edges form a matching

For an unsafe overlap pair u<v, the unique common retained completion word is
not arbitrary.

Unsafe gives

  incomingRetained(u) union outgoingRetained(v) = Fin n,

while overlap gives

  incomingRetained(u) inter outgoingRetained(v) = empty.

Hence the common completion word is exactly the characteristic Boolean word of
incomingRetained(u): true on incoming colours of u and false on the complementary
outgoing colours of v.

Therefore an unsafe overlap word is determined by its lower endpoint alone,
and also by its upper endpoint alone.

If one lower endpoint u belonged to two distinct unsafe overlap pairs u<v and
u<w, the two overlap words would coincide.  That one word would then lie in
the three completion cubes Q_u,Q_v,Q_w, contradicting multiplicity at most two.
The same argument applies to a common upper endpoint.

Thus unsafe overlap residual edges form a matching.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def incomingCharacteristic
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u : V) : Fin n → Bool :=
  fun c => decide (c ∈ incomingRetained C u)

/-- The unique unsafe-overlap word is the characteristic word of the lower
endpoint's incoming retained colours. -/
theorem unsafe_overlap_word_eq_incomingCharacteristic
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    word = incomingCharacteristic C u := by
  funext c
  by_cases hinc : c ∈ incomingRetained C u
  · have hactive :
        c ∈ retainedActive C u :=
      incomingRetained_subset_retainedActive C u hinc
    have hcomp :=
      (mem_retainedCompletionWords C u word).1 huWord c hactive
    have htrue :
        retainedBit C u c = true :=
      (mem_incomingRetained_iff_retainedBit_true C u c).1 hinc
    simp [incomingCharacteristic, hinc, hcomp, htrue]
  · have huniv :=
      unsafe_residual_union_eq_univ C hunsafe
    have hout :
        c ∈ outgoingRetained C v := by
      have hc :
          c ∈ incomingRetained C u ∪ outgoingRetained C v := by
        rw [huniv]
        simp
      rw [Finset.mem_union] at hc
      rcases hc with hinc' | hout
      · exact False.elim (hinc hinc')
      · exact hout
    have hactive :
        c ∈ retainedActive C v :=
      outgoingRetained_subset_retainedActive C v hout
    have hnotIncoming :
        c ∉ incomingRetained C v := by
      intro hvin
      exact Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C v)
        hvin hout
    have hfalse :
        retainedBit C v c = false := by
      unfold retainedBit
      apply bit_eq_false_iff.mpr
      intro hex
      exact hnotIncoming
        ((mem_incomingRetained_iff C v c).2 hex)
    have hcomp :=
      (mem_retainedCompletionWords C v word).1 hvWord c hactive
    simp [incomingCharacteristic, hinc, hcomp, hfalse]

/-- Equivalent upper-end characterization by the complement of outgoing
retained colours. -/
theorem unsafe_overlap_word_eq_not_outgoing
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    word =
      fun c => decide (c ∉ outgoingRetained C v) := by
  have hword :=
    unsafe_overlap_word_eq_incomingCharacteristic
      C hunsafe huWord hvWord
  rw [hword]
  funext c
  have huniv :=
    unsafe_residual_union_eq_univ C hunsafe
  have hthrough :=
    residualThroughColours_eq_empty_of_completion_overlap
      C huWord hvWord
  have hiff :
      c ∈ incomingRetained C u ↔
        c ∉ outgoingRetained C v := by
    constructor
    · intro hinc hout
      have hc :
          c ∈ residualThroughColours C u v :=
        (mem_residualThroughColours C u v c).2
          ⟨hinc, hout⟩
      rw [hthrough] at hc
      simp at hc
    · intro hnotOut
      have hc :
          c ∈ incomingRetained C u ∪ outgoingRetained C v := by
        rw [huniv]
        simp
      rw [Finset.mem_union] at hc
      rcases hc with hinc | hout
      · exact hinc
      · exact False.elim (hnotOut hout)
  simp [incomingCharacteristic, hiff]

/-- One lower endpoint has at most one unsafe-overlap partner. -/
theorem unsafe_overlap_upper_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V}
    {wordV wordW : Fin n → Bool}
    (huv : u < v)
    (huw : u < w)
    (hunsafeV :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (hunsafeW :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u w)
    (huV : wordV ∈ retainedCompletionWords C u)
    (hv : wordV ∈ retainedCompletionWords C v)
    (huW : wordW ∈ retainedCompletionWords C u)
    (hw : wordW ∈ retainedCompletionWords C w) :
    v = w := by
  have hwordV :=
    unsafe_overlap_word_eq_incomingCharacteristic
      C hunsafeV huV hv
  have hwordW :=
    unsafe_overlap_word_eq_incomingCharacteristic
      C hunsafeW huW hw
  have hwords : wordV = wordW :=
    hwordV.trans hwordW.symm
  subst wordW
  by_contra hvw
  exact no_three_distinct_share_retained_completion
    C (ne_of_lt huv) (ne_of_lt huw) hvw
    huV hv hw

/-- One upper endpoint has at most one unsafe-overlap partner. -/
theorem unsafe_overlap_lower_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u w v : V}
    {wordU wordW : Fin n → Bool}
    (huv : u < v)
    (hwv : w < v)
    (hunsafeU :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (hunsafeW :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C w v)
    (hu : wordU ∈ retainedCompletionWords C u)
    (hvU : wordU ∈ retainedCompletionWords C v)
    (hw : wordW ∈ retainedCompletionWords C w)
    (hvW : wordW ∈ retainedCompletionWords C v) :
    u = w := by
  have hwordU :=
    unsafe_overlap_word_eq_not_outgoing
      C hunsafeU hu hvU
  have hwordW :=
    unsafe_overlap_word_eq_not_outgoing
      C hunsafeW hw hvW
  have hwords : wordU = wordW :=
    hwordU.trans hwordW.symm
  subst wordW
  by_contra huw
  exact no_three_distinct_share_retained_completion
    C huw (ne_of_lt huv) (ne_of_lt hwv)
    hu hw hvU

/-- Edge-level matching statement: two unsafe overlapping residual edges that
share an endpoint are the same ordered pair. -/
theorem unsafe_overlap_edges_matching
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v a b : V}
    {word₁ word₂ : Fin n → Bool}
    (huv : u < v)
    (hab : a < b)
    (hunsafe₁ :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (hunsafe₂ :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C a b)
    (hu₁ : word₁ ∈ retainedCompletionWords C u)
    (hv₁ : word₁ ∈ retainedCompletionWords C v)
    (ha₂ : word₂ ∈ retainedCompletionWords C a)
    (hb₂ : word₂ ∈ retainedCompletionWords C b)
    (hshare : u = a ∨ u = b ∨ v = a ∨ v = b) :
    u = a ∧ v = b := by
  rcases hshare with hua | hub | hva | hvb
  · subst a
    have hvEq :=
      unsafe_overlap_upper_unique
        C huv hab hunsafe₁ hunsafe₂
        hu₁ hv₁ ha₂ hb₂
    exact ⟨rfl, hvEq⟩
  · subst b
    have hresAU :
        IsResidual C a u :=
      isResidual_of_retainedCompletion_overlap_lt
        C hab ha₂ hb₂
    have hresUV :
        IsResidual C u v :=
      isResidual_of_retainedCompletion_overlap_lt
        C huv hu₁ hv₁
    exact False.elim
      (no_two_residual_on_path C hab huv hresAU hresUV)
  · subst a
    have hresUV :
        IsResidual C u v :=
      isResidual_of_retainedCompletion_overlap_lt
        C huv hu₁ hv₁
    have hresVB :
        IsResidual C v b :=
      isResidual_of_retainedCompletion_overlap_lt
        C hab ha₂ hb₂
    exact False.elim
      (no_two_residual_on_path C huv hab hresUV hresVB)
  · subst b
    have huEq :=
      unsafe_overlap_lower_unique
        C huv hab hunsafe₁ hunsafe₂
        hu₁ hv₁ ha₂ hb₂
    exact ⟨huEq, rfl⟩

#print axioms unsafe_overlap_word_eq_incomingCharacteristic
#print axioms unsafe_overlap_upper_unique
#print axioms unsafe_overlap_lower_unique
#print axioms unsafe_overlap_edges_matching

end OrderedEdgeColoring
end JSP000404Research
