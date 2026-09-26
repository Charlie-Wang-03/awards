
import JSP000404Research.StandardResidualInterval
import JSP000404Research.ResidualUnsafeOverlapMatching
import Mathlib.Tactic

/-!
# Nested unsafe-overlap residual edges force a safe cross edge

Let u<a<b<v and suppose both outer pairs

  u--v,  a--b

are residual.

The standard residual interval theorem forces both cross edges

  u--b,  a--v

to be residual as well.

Now assume the two original residual edges are unsafe and carry projected
overlap words.  They are unit-defect carrier candidates.

The two cross residual edges cannot both be unsafe.  Indeed:

* unsafe u--v plus overlap gives
    incoming(u) disjoint outgoing(v), with union all colours;
* unsafe a--b plus overlap gives
    incoming(a) disjoint outgoing(b), with union all colours;
* unsafe a--v forces incoming(u) subset incoming(a);
* unsafe u--b forces incoming(a) subset incoming(u).

Hence incoming(u)=incoming(a).  The unique unsafe-overlap word is the
characteristic word of the lower incoming set, so the two original overlap
words are equal.  That one word would lie in the completion cubes of
u,a,v, contradicting completion multiplicity at most two.

Therefore every nested pair of unsafe-overlap carriers creates a safe cross
residual edge.  This is the first augmenting-path relation between distinct
unit defects.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- Two nested residual edges force both source-to-sink cross edges. -/
theorem standardResidual_nested_cross_edges
    {V : Type*} [LinearOrder V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hwidth : t < (n + 1 : ℕ))
    {u a b v : V}
    (hua : u < a)
    (hab : a < b)
    (hbv : b < v)
    (hresUV :
      IsResidual (standardResidualColoring D n hwidth) u v)
    (hresAB :
      IsResidual (standardResidualColoring D n hwidth) a b) :
    IsResidual (standardResidualColoring D n hwidth) u b ∧
      IsResidual (standardResidualColoring D n hwidth) a v := by
  let R := standardResidualColoring D n hwidth
  have haTrue :
      residualBit R a = true :=
    residualBit_eq_true_of_residual R hab hresAB
  have hbFalse :
      residualBit R b = false :=
    residualBit_eq_false_of_residual R hab hresAB
  have hub : u < b := hua.trans hab
  have hav : a < v := hab.trans hbv
  constructor
  · exact
      (standardResidual_left_child_iff_bit_false
        D hwidth hub hbv hresUV).2 hbFalse
  · exact
      (standardResidual_right_child_iff_bit_true
        D hwidth hua hav hresUV).2 haTrue

/-- Helper: unsafe overlap makes lower incoming and upper outgoing colours
disjoint. -/
theorem incoming_disjoint_outgoing_of_unsafe_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    Disjoint (incomingRetained C u) (outgoingRetained C v) := by
  classical
  rw [← Finset.inter_eq_empty]
  exact residualThroughColours_eq_empty_of_completion_overlap
    C huWord hvWord

/-- If both cross edges of two nested unsafe-overlap carriers were unsafe,
their lower incoming sets would coincide. -/
theorem nested_cross_both_unsafe_force_lower_incoming_eq
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u a b v : V}
    {wordUV wordAB : Fin n → Bool}
    (hunsafeUV :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (hunsafeAB :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C a b)
    (huWord : wordUV ∈ retainedCompletionWords C u)
    (hvWord : wordUV ∈ retainedCompletionWords C v)
    (haWord : wordAB ∈ retainedCompletionWords C a)
    (hbWord : wordAB ∈ retainedCompletionWords C b)
    (hunsafeUB :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u b)
    (hunsafeAV :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C a v) :
    incomingRetained C u = incomingRetained C a := by
  classical
  have hpartUV :
      Disjoint (incomingRetained C u) (outgoingRetained C v) :=
    incoming_disjoint_outgoing_of_unsafe_overlap
      C huWord hvWord
  have hpartAB :
      Disjoint (incomingRetained C a) (outgoingRetained C b) :=
    incoming_disjoint_outgoing_of_unsafe_overlap
      C haWord hbWord
  have hunionUB :=
    unsafe_residual_union_eq_univ C hunsafeUB
  have hunionAV :=
    unsafe_residual_union_eq_univ C hunsafeAV
  apply Finset.Subset.antisymm
  · intro c hcu
    have hnotOv : c ∉ outgoingRetained C v := by
      intro hcv
      exact Finset.disjoint_left.mp hpartUV hcu hcv
    have hc :
        c ∈ incomingRetained C a ∪ outgoingRetained C v := by
      rw [hunionAV]
      simp
    rw [Finset.mem_union] at hc
    rcases hc with hca | hcv
    · exact hca
    · exact False.elim (hnotOv hcv)
  · intro c hca
    have hnotOb : c ∉ outgoingRetained C b := by
      intro hcb
      exact Finset.disjoint_left.mp hpartAB hca hcb
    have hc :
        c ∈ incomingRetained C u ∪ outgoingRetained C b := by
      rw [hunionUB]
      simp
    rw [Finset.mem_union] at hc
    rcases hc with hcu | hcb
    · exact hcu
    · exact False.elim (hnotOb hcb)

/-- Main nested repair theorem: at least one forced cross residual edge has a
safe retained target colour. -/
theorem nested_unsafe_overlap_has_safe_cross
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hwidth : t < (n + 1 : ℕ))
    {u a b v : V}
    (hua : u < a)
    (hab : a < b)
    (hbv : b < v)
    {wordUV wordAB : Fin n → Bool}
    (hunsafeUV :
      ¬ ∃ c : Fin n,
        c ∉ residualForbidden
          (standardResidualColoring D n hwidth) u v)
    (hunsafeAB :
      ¬ ∃ c : Fin n,
        c ∉ residualForbidden
          (standardResidualColoring D n hwidth) a b)
    (huWord :
      wordUV ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) u)
    (hvWord :
      wordUV ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) v)
    (haWord :
      wordAB ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) a)
    (hbWord :
      wordAB ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) b) :
    (∃ c : Fin n,
      c ∉ residualForbidden
        (standardResidualColoring D n hwidth) u b)
    ∨
    (∃ c : Fin n,
      c ∉ residualForbidden
        (standardResidualColoring D n hwidth) a v) := by
  let R := standardResidualColoring D n hwidth
  have hresUV :
      IsResidual R u v :=
    isResidual_of_retainedCompletion_overlap_lt
      R (hua.trans (hab.trans hbv)) huWord hvWord
  have hresAB :
      IsResidual R a b :=
    isResidual_of_retainedCompletion_overlap_lt
      R hab haWord hbWord
  have _hcross :=
    standardResidual_nested_cross_edges
      D hwidth hua hab hbv hresUV hresAB
  by_contra hsafe
  push_neg at hsafe
  have hunsafeUB :
      ¬ ∃ c : Fin n, c ∉ residualForbidden R u b := by
    push_neg
    exact hsafe.1
  have hunsafeAV :
      ¬ ∃ c : Fin n, c ∉ residualForbidden R a v := by
    push_neg
    exact hsafe.2
  have hInEq :
      incomingRetained R u =
        incomingRetained R a :=
    nested_cross_both_unsafe_force_lower_incoming_eq
      R hunsafeUV hunsafeAB
      huWord hvWord haWord hbWord
      hunsafeUB hunsafeAV
  have hcharEq :
      incomingCharacteristic R u =
        incomingCharacteristic R a := by
    funext c
    simp [incomingCharacteristic, hInEq]
  have hwordUV :=
    unsafe_overlap_word_eq_incomingCharacteristic
      R hunsafeUV huWord hvWord
  have hwordAB :=
    unsafe_overlap_word_eq_incomingCharacteristic
      R hunsafeAB haWord hbWord
  have hwords :
      wordUV = wordAB := by
    rw [hwordUV, hwordAB, hcharEq]
  subst wordAB
  exact no_three_distinct_share_retained_completion
    R (ne_of_lt hua)
      (ne_of_lt (hua.trans (hab.trans hbv)))
      (ne_of_lt (hab.trans hbv))
      huWord haWord hvWord

#print axioms standardResidual_nested_cross_edges
#print axioms nested_cross_both_unsafe_force_lower_incoming_eq
#print axioms nested_unsafe_overlap_has_safe_cross

end DirectionData
end JSP000404Research
