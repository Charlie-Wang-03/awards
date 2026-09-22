
import JSP000404Research.ResidualOverlapDichotomy
import Mathlib.Tactic

/-!
# Exact Boolean dimension of a projected overlap carrier

Let Q_u and Q_v be two retained completion cubes with at least one common
word base.

A coordinate is free in their intersection exactly when it is inactive at
both endpoints.  Equivalently it lies outside

  retainedActive(u) union retainedActive(v).

All coordinates in the active union are forced to their value in base; the
existence of base guarantees consistency where both endpoints are active.

Hence Q_u inter Q_v is itself a Boolean subcube of exact cardinality

  2^(n - card(active_u union active_v)).

This is the exact overlap mass carried by one residual pair.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def commonRetainedInactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) : Finset (Fin n) := by
  classical
  exact Finset.univ \ (retainedActive C u ∪ retainedActive C v)

@[simp] theorem mem_commonRetainedInactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c : Fin n) :
    c ∈ commonRetainedInactive C u v ↔
      c ∉ retainedActive C u ∧
      c ∉ retainedActive C v := by
  classical
  simp [commonRetainedInactive]

theorem commonRetainedInactive_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (commonRetainedInactive C u v).card =
      n - (retainedActive C u ∪
        retainedActive C v).card := by
  classical
  unfold commonRetainedInactive
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

/-- The intersection completion condition is exactly agreement with one common
base word on the union of the two active sets. -/
theorem mem_completion_inter_iff_eq_base_on_active_union
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base word : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v) :
    word ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v
      ↔
    ∀ c, c ∈ retainedActive C u ∪ retainedActive C v →
      word c = base c := by
  constructor
  · intro hword c hc
    have hparts := Finset.mem_inter.mp hword
    have hu :=
      (mem_retainedCompletionWords C u word).1 hparts.1
    have hv :=
      (mem_retainedCompletionWords C v word).1 hparts.2
    have hbu :=
      (mem_retainedCompletionWords C u base).1 hbaseU
    have hbv :=
      (mem_retainedCompletionWords C v base).1 hbaseV
    rw [Finset.mem_union] at hc
    rcases hc with hcu | hcv
    · exact (hu c hcu).trans (hbu c hcu).symm
    · exact (hv c hcv).trans (hbv c hcv).symm
  · intro hword
    apply Finset.mem_inter.mpr
    constructor
    · apply (mem_retainedCompletionWords C u word).2
      intro c hc
      have hw := hword c (Finset.mem_union_left _ hc)
      have hb :=
        (mem_retainedCompletionWords C u base).1 hbaseU c hc
      exact hw.trans hb
    · apply (mem_retainedCompletionWords C v word).2
      intro c hc
      have hw := hword c (Finset.mem_union_right _ hc)
      have hb :=
        (mem_retainedCompletionWords C v base).1 hbaseV c hc
      exact hw.trans hb

/-- Free assignments on the common inactive coordinates parameterize the
intersection cube. -/
noncomputable def overlapEquivCommonInactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v) :
    (commonRetainedInactive C u v → Bool) ≃
      {word : Fin n → Bool //
        word ∈ retainedCompletionWords C u ∩
          retainedCompletionWords C v} where
  toFun free := ⟨
    fun c =>
      if hc : c ∈ retainedActive C u ∪ retainedActive C v then
        base c
      else
        free ⟨c, by
          exact (mem_commonRetainedInactive C u v c).2
            (by
              rw [Finset.mem_union] at hc
              push_neg at hc
              exact hc)⟩,
    by
      apply (mem_completion_inter_iff_eq_base_on_active_union
        C hbaseU hbaseV).2
      intro c hc
      simp [hc]⟩
  invFun word :=
    fun c => word.1 c.1
  left_inv free := by
    funext c
    have hc :
        c.1 ∉ retainedActive C u ∪ retainedActive C v := by
      rw [Finset.mem_union]
      push_neg
      exact (mem_commonRetainedInactive C u v c.1).1 c.2
    simp [hc]
  right_inv word := by
    apply Subtype.ext
    funext c
    by_cases hc :
        c ∈ retainedActive C u ∪ retainedActive C v
    · have hfix :=
        (mem_completion_inter_iff_eq_base_on_active_union
          C hbaseU hbaseV).1 word.2 c hc
      simp [hc, hfix]
    · simp [hc]

/-- Exact cardinality of one nonempty pairwise projected overlap. -/
theorem retainedCompletionWords_inter_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v) :
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card =
      2 ^ (commonRetainedInactive C u v).card := by
  classical
  have hcard :=
    Fintype.card_congr
      (overlapEquivCommonInactive C hbaseU hbaseV)
  have hleft :
      Fintype.card (commonRetainedInactive C u v → Bool) =
        2 ^ (commonRetainedInactive C u v).card := by
    simp [Fintype.card_fun]
  rw [hleft] at hcard
  simpa using hcard.symm

/-- Equivalent active-union dimension formula. -/
theorem retainedCompletionWords_inter_card_eq_pow_union_complement
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v) :
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card =
      2 ^ (n - (retainedActive C u ∪
        retainedActive C v).card) := by
  rw [retainedCompletionWords_inter_card
      C hbaseU hbaseV,
    commonRetainedInactive_card]

/-- Unsafe overlap is exactly the zero-dimensional case of the general overlap
cube formula. -/
theorem commonRetainedInactive_eq_empty_of_unsafe
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    commonRetainedInactive C u v = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c _
  have hcover :=
    retainedActive_union_eq_univ_of_unsafe C hunsafe
  intro hc
  have hcmissing :=
    (mem_commonRetainedInactive C u v c).1 hc
  have hcUnion :
      c ∈ retainedActive C u ∪ retainedActive C v := by
    rw [hcover]
    simp
  rw [Finset.mem_union] at hcUnion
  exact hcUnion.elim hcmissing.1 hcmissing.2

#print axioms mem_completion_inter_iff_eq_base_on_active_union
#print axioms retainedCompletionWords_inter_card
#print axioms retainedCompletionWords_inter_card_eq_pow_union_complement
#print axioms commonRetainedInactive_eq_empty_of_unsafe

end OrderedEdgeColoring
end JSP000404Research
