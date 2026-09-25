
import JSP000404Research.ResidualOverlapRigidity
import JSP000404Research.WeightedHansel
import Mathlib.Tactic

/-!
# Exact dimension of a projected overlap cube

If a retained word belongs to both completion cubes Q_u and Q_v, then the two
partial assignments are compatible on every retained coordinate active at
both endpoints.

Hence the entire intersection Q_u inter Q_v is exactly one Boolean subcube.
Its free coordinates are precisely those retained colours which are inactive
at both u and v.

Therefore

  card (Q_u inter Q_v)
    = 2 ^ card(commonInactive(u,v)).

This gives an exact edgewise decomposition of projected overlap mass.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def commonInactiveRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun c =>
    c ∉ retainedActive C u ∧
    c ∉ retainedActive C v

@[simp] theorem mem_commonInactiveRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c : Fin n) :
    c ∈ commonInactiveRetained C u v ↔
      c ∉ retainedActive C u ∧
      c ∉ retainedActive C v := by
  classical
  simp [commonInactiveRetained]

abbrev PairFreeCoordinates
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :=
  FreeCoordinates (retainedActive C u ∪ retainedActive C v)

/-- A common completion word identifies the intersection with the free
coordinates outside the union of the two retained active sets. -/
noncomputable def retainedPairIntersectionEquivFree
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (base : Fin n → Bool)
    (hu : base ∈ retainedCompletionWords C u)
    (hv : base ∈ retainedCompletionWords C v) :
    PairFreeCoordinates C u v ≃
      {x : Fin n → Bool //
        x ∈ retainedCompletionWords C u ∩
          retainedCompletionWords C v} where
  toFun free := ⟨
    fun c =>
      if hc : c ∈ retainedActive C u ∪ retainedActive C v then
        base c
      else
        free ⟨c, hc⟩,
    by
      rw [Finset.mem_inter]
      constructor
      · apply (mem_retainedCompletionWords C u _).2
        intro c hcu
        have hUnion :
            c ∈ retainedActive C u ∪ retainedActive C v :=
          Finset.mem_union_left _ hcu
        simp [hUnion]
        exact
          (mem_retainedCompletionWords C u base).1 hu c hcu
      · apply (mem_retainedCompletionWords C v _).2
        intro c hcv
        have hUnion :
            c ∈ retainedActive C u ∪ retainedActive C v :=
          Finset.mem_union_right _ hcv
        simp [hUnion]
        exact
          (mem_retainedCompletionWords C v base).1 hv c hcv⟩
  invFun x :=
    fun c => x.1 c.1
  left_inv free := by
    funext c
    simp [PairFreeCoordinates, c.2]
  right_inv x := by
    apply Subtype.ext
    funext c
    by_cases hc :
        c ∈ retainedActive C u ∪ retainedActive C v
    · simp [hc]
      rw [Finset.mem_union] at hc
      rcases hc with hcu | hcv
      · have hxU :
            RetainedCompletes C u x.1 :=
          (mem_retainedCompletionWords C u x.1).1
            (Finset.mem_inter.mp x.2).1
        have hbU :
            RetainedCompletes C u base :=
          (mem_retainedCompletionWords C u base).1 hu
        exact (hbU c hcu).trans (hxU c hcu).symm
      · have hxV :
            RetainedCompletes C v x.1 :=
          (mem_retainedCompletionWords C v x.1).1
            (Finset.mem_inter.mp x.2).2
        have hbV :
            RetainedCompletes C v base :=
          (mem_retainedCompletionWords C v base).1 hv
        exact (hbV c hcv).trans (hxV c hcv).symm
    · simp [hc]

/-- Complement-card form for common inactive coordinates. -/
theorem commonInactiveRetained_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (commonInactiveRetained C u v).card =
      n - (retainedActive C u ∪ retainedActive C v).card := by
  classical
  have hsub :
      retainedActive C u ∪ retainedActive C v ⊆
        (Finset.univ : Finset (Fin n)) := by
    simp
  have hcard :=
    Finset.card_sdiff_add_card_eq_card
      hsub
  have hEq :
      commonInactiveRetained C u v =
        (Finset.univ : Finset (Fin n)) \
          (retainedActive C u ∪ retainedActive C v) := by
    ext c
    simp [commonInactiveRetained]
  rw [hEq]
  have huniv :
      (Finset.univ : Finset (Fin n)).card = n := by simp
  omega

/-- Exact cardinality of a nonempty projected pair intersection. -/
theorem retainedCompletionWords_inter_card_eq_pow_commonInactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {base : Fin n → Bool}
    (hu : base ∈ retainedCompletionWords C u)
    (hv : base ∈ retainedCompletionWords C v) :
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card =
      2 ^ (commonInactiveRetained C u v).card := by
  classical
  have hcard :=
    Fintype.card_congr
      (retainedPairIntersectionEquivFree C base hu hv)
  rw [card_freeCoordinates] at hcard
  rw [commonInactiveRetained_card C u v]
  simpa using hcard.symm

/-- More than one overlap word is equivalent to the existence of a common
inactive retained coordinate. -/
theorem one_lt_inter_card_iff_commonInactive_nonempty
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {base : Fin n → Bool}
    (hu : base ∈ retainedCompletionWords C u)
    (hv : base ∈ retainedCompletionWords C v) :
    1 <
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
      ↔
    (commonInactiveRetained C u v).Nonempty := by
  rw [retainedCompletionWords_inter_card_eq_pow_commonInactive
      C hu hv]
  constructor
  · intro h
    have hpos :
        0 < (commonInactiveRetained C u v).card := by
      by_contra hzero
      have hz :
          (commonInactiveRetained C u v).card = 0 := by omega
      rw [hz] at h
      norm_num at h
    exact Finset.card_pos.mp hpos
  · intro hne
    have hpos :
        0 < (commonInactiveRetained C u v).card :=
      Finset.card_pos.mpr hne
    have hp :
        2 ^ 0 < 2 ^ (commonInactiveRetained C u v).card :=
      Nat.pow_lt_pow_right (by norm_num : 1 < 2) hpos
    simpa using hp

/-- Every exponential overlap edge has a common inactive safe retained colour. -/
theorem exists_common_inactive_of_one_lt_overlap_inter
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {base : Fin n → Bool}
    (hu : base ∈ retainedCompletionWords C u)
    (hv : base ∈ retainedCompletionWords C v)
    (hmulti :
      1 <
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card) :
    ∃ c : Fin n,
      c ∉ retainedActive C u ∧
      c ∉ retainedActive C v ∧
      c ∉ residualForbidden C u v := by
  have hne :
      (commonInactiveRetained C u v).Nonempty :=
    (one_lt_inter_card_iff_commonInactive_nonempty
      C hu hv).1 hmulti
  obtain ⟨c, hc⟩ := hne
  have hc' :=
    (mem_commonInactiveRetained C u v c).1 hc
  refine ⟨c, hc'.1, hc'.2, ?_⟩
  intro hforbid
  rw [residualForbidden, Finset.mem_union] at hforbid
  rcases hforbid with hIn | hOut
  · exact hc'.1 (incomingRetained_subset_retainedActive C u hIn)
  · exact hc'.2 (outgoingRetained_subset_retainedActive C v hOut)

#print axioms retainedCompletionWords_inter_card_eq_pow_commonInactive
#print axioms one_lt_inter_card_iff_commonInactive_nonempty
#print axioms exists_common_inactive_of_one_lt_overlap_inter

end OrderedEdgeColoring
end JSP000404Research
