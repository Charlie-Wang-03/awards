import JSP000404Research.ResidualSafeCommonInactiveRigidity
import JSP000404Research.ResidualUnsafeOverlapMatching
import Mathlib.Tactic

/-!
# Support-unsafe overlap carriers form a matching

The common-inactive tensor does not destroy the matching rigidity of unsafe
overlaps.

For a no-active-safe overlap pair u<v, define the lower canonical word by the
incoming characteristic of u.  This is simply the completion word of u with
all u-free coordinates set to false.  Support-unsafety forces every coordinate
active only at v to be outgoing at v, hence also false.  Therefore this one
word belongs to both Q_u and Q_v and depends only on u.

Dually, the upper canonical word is the complement of the outgoing
characteristic of v: all v-free coordinates are set to true.  It belongs to
both endpoint cubes and depends only on v.

Consequently one lower endpoint cannot have two distinct support-unsafe
overlap partners, and one upper endpoint cannot have two distinct partners:
the endpoint-canonical word would lie in three completion cubes.  Crossed
shared endpoints are excluded by the residual no-two-path condition.

Thus support-unsafe overlap carrier edges form a genuine matching, exactly as
fully unsafe carriers do.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def notOutgoingCharacteristic
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) : Fin n → Bool :=
  fun c => decide (c ∉ outgoingRetained C v)

theorem incomingCharacteristic_mem_left_completion
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u : V) :
    incomingCharacteristic C u ∈ retainedCompletionWords C u := by
  apply (mem_retainedCompletionWords C u _).2
  intro c hc
  rw [retainedActive_eq_incoming_union_outgoing C u] at hc
  rcases Finset.mem_union.mp hc with hIn | hOut
  · have htrue :
        retainedBit C u c = true :=
      (mem_incomingRetained_iff_retainedBit_true C u c).1 hIn
    simp [incomingCharacteristic,hIn,htrue]
  · have hnotIn : c ∉ incomingRetained C u := by
      intro hIn
      exact Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C u)
        hIn hOut
    have hfalse :
        retainedBit C u c = false := by
      exact retainedBit_false_of_outgoingRetained C hOut
    simp [incomingCharacteristic,hnotIn,hfalse]

theorem incomingCharacteristic_mem_right_of_noActiveSafe_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v) :
    incomingCharacteristic C u ∈ retainedCompletionWords C v := by
  apply (mem_retainedCompletionWords C v _).2
  intro c hcV
  by_cases hcU : c ∈ retainedActive C u
  · have huComp :=
      (mem_retainedCompletionWords C u base).1 huBase
    have hvComp :=
      (mem_retainedCompletionWords C v base).1 hvBase
    have hbits :
        retainedBit C u c = retainedBit C v c :=
      (huComp c hcU).symm.trans (hvComp c hcV)
    rw [← hbits]
    rw [retainedActive_eq_incoming_union_outgoing C u] at hcU
    rcases Finset.mem_union.mp hcU with hIn | hOut
    · have htrue :=
        (mem_incomingRetained_iff_retainedBit_true C u c).1 hIn
      simp [incomingCharacteristic,hIn,htrue]
    · have hnotIn : c ∉ incomingRetained C u := by
        intro hIn
        exact Finset.disjoint_left.mp
          (incomingRetained_disjoint_outgoingRetained C u)
          hIn hOut
      have hfalse :=
        retainedBit_false_of_outgoingRetained C hOut
      simp [incomingCharacteristic,hnotIn,hfalse]
  · have hcUnion :
        c ∈ retainedActive C u ∪ retainedActive C v :=
      Finset.mem_union_right _ hcV
    have hcForbid :
        c ∈ residualForbidden C u v := by
      rw [residualForbidden_eq_active_union_of_noActiveSafe C hno]
      exact hcUnion
    unfold residualForbidden at hcForbid
    rw [Finset.mem_union] at hcForbid
    rcases hcForbid with hInU | hOutV
    · exact False.elim
        (hcU (incomingRetained_subset_retainedActive C u hInU))
    · have hnotInU : c ∉ incomingRetained C u := by
        intro hInU
        exact hcU
          (incomingRetained_subset_retainedActive C u hInU)
      have hfalse :=
        retainedBit_false_of_outgoingRetained C hOutV
      simp [incomingCharacteristic,hnotInU,hfalse]

theorem notOutgoingCharacteristic_mem_right_completion
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    notOutgoingCharacteristic C v ∈ retainedCompletionWords C v := by
  apply (mem_retainedCompletionWords C v _).2
  intro c hc
  rw [retainedActive_eq_incoming_union_outgoing C v] at hc
  rcases Finset.mem_union.mp hc with hIn | hOut
  · have hnotOut : c ∉ outgoingRetained C v := by
      intro hOut
      exact Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C v)
        hIn hOut
    have htrue :=
      (mem_incomingRetained_iff_retainedBit_true C v c).1 hIn
    simp [notOutgoingCharacteristic,hnotOut,htrue]
  · have hfalse :=
      retainedBit_false_of_outgoingRetained C hOut
    simp [notOutgoingCharacteristic,hOut,hfalse]

theorem notOutgoingCharacteristic_mem_left_of_noActiveSafe_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (hno : NoActiveSafeCoordinate C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v) :
    notOutgoingCharacteristic C v ∈ retainedCompletionWords C u := by
  apply (mem_retainedCompletionWords C u _).2
  intro c hcU
  by_cases hcV : c ∈ retainedActive C v
  · have huComp :=
      (mem_retainedCompletionWords C u base).1 huBase
    have hvComp :=
      (mem_retainedCompletionWords C v base).1 hvBase
    have hbits :
        retainedBit C v c = retainedBit C u c :=
      (hvComp c hcV).symm.trans (huComp c hcU)
    rw [← hbits]
    rw [retainedActive_eq_incoming_union_outgoing C v] at hcV
    rcases Finset.mem_union.mp hcV with hIn | hOut
    · have hnotOut : c ∉ outgoingRetained C v := by
        intro hOut
        exact Finset.disjoint_left.mp
          (incomingRetained_disjoint_outgoingRetained C v)
          hIn hOut
      have htrue :=
        (mem_incomingRetained_iff_retainedBit_true C v c).1 hIn
      simp [notOutgoingCharacteristic,hnotOut,htrue]
    · have hfalse :=
        retainedBit_false_of_outgoingRetained C hOut
      simp [notOutgoingCharacteristic,hOut,hfalse]
  · have hcUnion :
        c ∈ retainedActive C u ∪ retainedActive C v :=
      Finset.mem_union_left _ hcU
    have hcForbid :
        c ∈ residualForbidden C u v := by
      rw [residualForbidden_eq_active_union_of_noActiveSafe C hno]
      exact hcUnion
    unfold residualForbidden at hcForbid
    rw [Finset.mem_union] at hcForbid
    rcases hcForbid with hInU | hOutV
    · have hnotOutV : c ∉ outgoingRetained C v := by
        intro hOutV
        exact hcV
          (outgoingRetained_subset_retainedActive C v hOutV)
      have htrue :=
        (mem_incomingRetained_iff_retainedBit_true C u c).1 hInU
      simp [notOutgoingCharacteristic,hnotOutV,htrue]
    · exact False.elim
        (hcV (outgoingRetained_subset_retainedActive C v hOutV))

theorem noActiveSafe_overlap_upper_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V}
    (huv : u < v)
    (huw : u < w)
    {baseV baseW : Fin n → Bool}
    (hnoV : NoActiveSafeCoordinate C u v)
    (hnoW : NoActiveSafeCoordinate C u w)
    (huV : baseV ∈ retainedCompletionWords C u)
    (hv : baseV ∈ retainedCompletionWords C v)
    (huW : baseW ∈ retainedCompletionWords C u)
    (hw : baseW ∈ retainedCompletionWords C w) :
    v = w := by
  have hcanonU :=
    incomingCharacteristic_mem_left_completion C u
  have hcanonV :=
    incomingCharacteristic_mem_right_of_noActiveSafe_overlap
      C hnoV huV hv
  have hcanonW :=
    incomingCharacteristic_mem_right_of_noActiveSafe_overlap
      C hnoW huW hw
  by_contra hvw
  exact no_three_distinct_share_retained_completion
    C (ne_of_lt huv) (ne_of_lt huw) hvw
    hcanonU hcanonV hcanonW

theorem noActiveSafe_overlap_lower_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u w v : V}
    (huv : u < v)
    (hwv : w < v)
    {baseU baseW : Fin n → Bool}
    (hnoU : NoActiveSafeCoordinate C u v)
    (hnoW : NoActiveSafeCoordinate C w v)
    (hu : baseU ∈ retainedCompletionWords C u)
    (hvU : baseU ∈ retainedCompletionWords C v)
    (hw : baseW ∈ retainedCompletionWords C w)
    (hvW : baseW ∈ retainedCompletionWords C v) :
    u = w := by
  have hcanonV :=
    notOutgoingCharacteristic_mem_right_completion C v
  have hcanonU :=
    notOutgoingCharacteristic_mem_left_of_noActiveSafe_overlap
      C hnoU hu hvU
  have hcanonW :=
    notOutgoingCharacteristic_mem_left_of_noActiveSafe_overlap
      C hnoW hw hvW
  by_contra huw
  exact no_three_distinct_share_retained_completion
    C huw (ne_of_lt huv) (ne_of_lt hwv)
    hcanonU hcanonW hcanonV

theorem noActiveSafe_overlap_edges_matching
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v a b : V}
    (huv : u < v)
    (hab : a < b)
    {base₁ base₂ : Fin n → Bool}
    (hno₁ : NoActiveSafeCoordinate C u v)
    (hno₂ : NoActiveSafeCoordinate C a b)
    (hu₁ : base₁ ∈ retainedCompletionWords C u)
    (hv₁ : base₁ ∈ retainedCompletionWords C v)
    (ha₂ : base₂ ∈ retainedCompletionWords C a)
    (hb₂ : base₂ ∈ retainedCompletionWords C b)
    (hshare : u = a ∨ u = b ∨ v = a ∨ v = b) :
    u = a ∧ v = b := by
  have hresUV :=
    isResidual_of_retainedCompletion_overlap_lt
      C huv hu₁ hv₁
  have hresAB :=
    isResidual_of_retainedCompletion_overlap_lt
      C hab ha₂ hb₂
  rcases hshare with hua | hub | hva | hvb
  · subst a
    have hvEq :=
      noActiveSafe_overlap_upper_unique
        C huv hab hno₁ hno₂ hu₁ hv₁ ha₂ hb₂
    exact ⟨rfl,hvEq⟩
  · subst b
    exact False.elim
      (no_two_residual_on_path C hab huv hresAB hresUV)
  · subst a
    exact False.elim
      (no_two_residual_on_path C huv hab hresUV hresAB)
  · subst b
    have huEq :=
      noActiveSafe_overlap_lower_unique
        C huv hab hno₁ hno₂ hu₁ hv₁ ha₂ hb₂
    exact ⟨huEq,rfl⟩

#print axioms incomingCharacteristic_mem_right_of_noActiveSafe_overlap
#print axioms notOutgoingCharacteristic_mem_left_of_noActiveSafe_overlap
#print axioms noActiveSafe_overlap_upper_unique
#print axioms noActiveSafe_overlap_lower_unique
#print axioms noActiveSafe_overlap_edges_matching

end OrderedEdgeColoring
end JSP000404Research
