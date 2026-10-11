import JSP000404Research.ResidualHardOverlapCubeTransport
import Mathlib.Tactic

/-!
# Whole hard overlap face can only move into singleton or SOFT overlap

The flip transport Q_a ∩ Q_v -> Q_v \ Q_a is now classified
globally, not just within the upper vertex's cube.

If a and v share a canonical retained code, they are the ONLY
two vertices in that code fibre. Therefore a word belonging to Q_v
but not Q_a cannot be in ANY hard completion overlap cube: if it
were, the hard overlap's other endpoint would necessarily be a.

Hence the whole transported hard-overlap face is in the disjoint
union of globally singly-covered words and SOFT overlapped words.

All results remain conditional on an available outgoing/inactive
coordinate c. They do not claim that singly covered words are
uncovered Boolean holes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A retained canonical code has at most two vertices, with no
requirement that they occur in the same order. -/
theorem sameRetained_two_distinct_companions_equal
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a b v : V}
    (hav : a ≠ v)
    (hbv : b ≠ v)
    (ha : SameRetained C a v)
    (hb : SameRetained C b v) :
    a = b := by
  by_contra hab
  let word : Fin n → Bool := fun d => retainedBit C v d
  have hv : word ∈ retainedCompletionWords C v := by
    apply (mem_retainedCompletionWords C v word).2
    intro d hd
    rfl
  have haw : word ∈ retainedCompletionWords C a := by
    apply (mem_retainedCompletionWords C a word).2
    intro d hd
    exact (ha d).symm
  have hbw : word ∈ retainedCompletionWords C b := by
    apply (mem_retainedCompletionWords C b word).2
    intro d hd
    exact (hb d).symm
  exact no_three_distinct_share_retained_completion
    C hab hav hbv haw hbw hv

/-- If a and v form a same-code hard pair, EVERY Boolean word in
the upper completion cube but outside the lower one is excluded
from ALL hard overlap cubes (not merely from Q_a inter Q_v). -/
theorem hard_pair_upper_only_not_hard_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V}
    (hav : a ≠ v)
    (hsame : SameRetained C a v)
    {word : Fin n → Bool}
    (hvword : word ∈ retainedCompletionWords C v)
    (hnotA : word ∉ retainedCompletionWords C a) :
    word ∉ hardOverlapCompletionWords C := by
  classical
  intro hhard
  obtain ⟨p,hp,hpword⟩ := Finset.mem_biUnion.mp hhard
  have hpdata := (mem_hardOverlapCarrierPairs C p).1 hp
  have hpres := (mem_overlapCarrierPairs C p).1 hpdata.1
  have hporder :=
    ((mem_residualCarrierPairs C p.1 p.2).1 hpres.1).1
  have hsamep := hpdata.2
  have hpwords := Finset.mem_inter.mp hpword
  by_cases hleft : v = p.1
  · have hother : SameRetained C p.2 v := by
      intro d
      calc
        retainedBit C p.2 d = retainedBit C p.1 d :=
          (hsamep d).symm
        _ = retainedBit C v d := by rw [hleft]
    have hne : p.2 ≠ v := by
      intro h
      rw [h, hleft] at hporder
      exact (lt_irrefl _) hporder
    have heq := sameRetained_two_distinct_companions_equal
      C hav hne hsame hother
    have hw : word ∈ retainedCompletionWords C a := by
      rw [heq]
      exact hpwords.2
    exact hnotA hw
  · by_cases hright : v = p.2
    · have hother : SameRetained C p.1 v := by
        intro d
        calc
          retainedBit C p.1 d = retainedBit C p.2 d :=
            hsamep d
          _ = retainedBit C v d := by rw [hright]
      have hne : p.1 ≠ v := by
        intro h
        rw [h, ← hright] at hporder
        exact (lt_irrefl _) hporder
      have heq := sameRetained_two_distinct_companions_equal
        C hav hne hsame hother
      have hw : word ∈ retainedCompletionWords C a := by
        rw [heq]
        exact hpwords.1
      exact hnotA hw
    · exact no_three_distinct_share_retained_completion
        C (ne_of_lt hporder) (Ne.symm hleft) (Ne.symm hright)
        hpwords.1 hpwords.2 hvword

/-- After flipping ANY word of the full same-code overlap face,
its new word CANNOT be a hard overlap word anywhere globally. -/
theorem hard_overlap_full_face_flip_not_hard
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V} {c : Fin n} {word : Fin n → Bool}
    (hav : a ≠ v)
    (hsame : SameRetained C a v)
    (hcOutgoing : c ∈ outgoingRetained C a)
    (hcInactive : c ∉ retainedActive C v)
    (hw : word ∈ retainedCompletionWords C a ∩
      retainedCompletionWords C v) :
    flipCompletionWord c word ∉ hardOverlapCompletionWords C := by
  have ht := hard_overlap_cube_flip_mem_upper_only C
    hcOutgoing hcInactive hw
  exact hard_pair_upper_only_not_hard_overlap C hav hsame
    (Finset.mem_sdiff.mp ht).1 (Finset.mem_sdiff.mp ht).2

/-- Globally singly-covered (multiplicity exactly one) words. -/
noncomputable def singletonCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter
    (fun word => (completionFibre C word).card = 1)

@[simp] theorem mem_singletonCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (word : Fin n → Bool) :
    word ∈ singletonCompletionWords C ↔
      (completionFibre C word).card = 1 := by
  classical
  simp [singletonCompletionWords]

/-- Every covered completion word which is not in a hard
overlap is either singly covered or in the global SOFT
overlap set; no additional third category exists. -/
theorem covered_not_hard_singleton_or_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {word : Fin n → Bool}
    (hcover : word ∈ coveredCompletionWords C)
    (hnotHard : word ∉ hardOverlapCompletionWords C) :
    word ∈ singletonCompletionWords C ∪
      softOverlapCompletionWords C := by
  have hpos :
      0 < (completionFibre C word).card :=
    Finset.card_pos.mpr ((mem_coveredCompletionWords C word).1 hcover)
  have hle := completionFibre_card_le_two C word
  have hcase :
      (completionFibre C word).card = 1 ∨
      (completionFibre C word).card = 2 := by
    omega
  rcases hcase with hsingle | hdouble
  · exact Finset.mem_union.mpr (Or.inl
      ((mem_singletonCompletionWords C word).2 hsingle))
  · have hmem := (mem_overlapCompletionWords C word).2 hdouble
    have hpart := (overlapCompletionWords_eq_hard_union_soft C)
    rw [hpart] at hmem
    exact Finset.mem_union.mpr
      (Or.inr ((Finset.mem_union.mp hmem).resolve_left hnotHard))

/-- A WHOLE hard completion-overlap face is transported into
globally singly-covered or SOFT overlap words, never into a hole. -/
theorem hard_overlap_full_face_flip_singleton_or_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V} {c : Fin n} {word : Fin n → Bool}
    (hav : a ≠ v)
    (hsame : SameRetained C a v)
    (hcOutgoing : c ∈ outgoingRetained C a)
    (hcInactive : c ∉ retainedActive C v)
    (hw : word ∈ retainedCompletionWords C a ∩
      retainedCompletionWords C v) :
    flipCompletionWord c word ∈
      singletonCompletionWords C ∪
        softOverlapCompletionWords C := by
  have hdest := hard_overlap_cube_flip_mem_upper_only C
    hcOutgoing hcInactive hw
  have hvword := (Finset.mem_sdiff.mp hdest).1
  have hcovered :
      flipCompletionWord c word ∈ coveredCompletionWords C :=
    (mem_coveredCompletionWords C _).2
      ⟨v, (mem_completionFibre C _ v).2 hvword⟩
  exact covered_not_hard_singleton_or_soft C hcovered
    (hard_overlap_full_face_flip_not_hard
      C hav hsame hcOutgoing hcInactive hw)

/-- Quantitative WHOLE-FACE relocation: an outward/inactive
colour of a same-code pair provides at least the entire original
hard-overlap mass in the union of SINGLETON or SOFT-OVERLAP
completion words. This is a local face bound (not summed across
different hard pairs, whose image sets may intersect). -/
theorem hard_overlap_face_mass_le_singleton_add_soft_global
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V} {c : Fin n}
    (hav : a ≠ v)
    (hsame : SameRetained C a v)
    (hcOutgoing : c ∈ outgoingRetained C a)
    (hcInactive : c ∉ retainedActive C v) :
    (retainedCompletionWords C a ∩
      retainedCompletionWords C v).card ≤
        (singletonCompletionWords C).card +
          (softOverlapCompletionWords C).card := by
  classical
  let f :
      {word : Fin n → Bool // word ∈
        retainedCompletionWords C a ∩ retainedCompletionWords C v} →
      {word : Fin n → Bool // word ∈
        singletonCompletionWords C ∪ softOverlapCompletionWords C} :=
    fun x => ⟨flipCompletionWord c x.1,
      hard_overlap_full_face_flip_singleton_or_soft
        C hav hsame hcOutgoing hcInactive x.2⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact flipCompletionWord_injective c
      (congrArg Subtype.val hxy)
  have hcard := Fintype.card_le_of_injective f hinj
  have hbound :
      (retainedCompletionWords C a ∩
          retainedCompletionWords C v).card ≤
        (singletonCompletionWords C ∪
          softOverlapCompletionWords C).card := by
    simpa only [Fintype.card_coe] using hcard
  have hunion := Finset.card_union_le
    (singletonCompletionWords C) (softOverlapCompletionWords C)
  omega

#print axioms sameRetained_two_distinct_companions_equal
#print axioms hard_pair_upper_only_not_hard_overlap
#print axioms hard_overlap_full_face_flip_not_hard
#print axioms covered_not_hard_singleton_or_soft
#print axioms hard_overlap_full_face_flip_singleton_or_soft
#print axioms hard_overlap_face_mass_le_singleton_add_soft_global

end OrderedEdgeColoring
end JSP000404Research
