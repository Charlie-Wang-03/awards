import JSP000404Research.ResidualTranslatedOverlapCaptureDichotomy
import Mathlib.Tactic

/-!
# Full-free blockers capture the entire translated overlap cube

Two words in the same pairwise completion intersection can differ only on
coordinates inactive at both endpoints.  Consequently, if a blocker is
inactive on every common-inactive source coordinate, then membership of one
translated source word forces membership of every translated source word.

Combined with the half-capture theorem, blocker capture has the sharp shape

  empty / full / at most half.

This is the key rigidity behind a dyadic collision tree.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem overlap_words_eq_off_commonInactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {x y : Fin n → Bool}
    (hx :
      x ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hy :
      y ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    {e : Fin n}
    (he :
      e ∉ commonInactiveRetained C u v) :
    x e = y e := by
  have hxParts := Finset.mem_inter.mp hx
  have hyParts := Finset.mem_inter.mp hy
  by_cases heu : e ∈ retainedActive C u
  · have hxU :=
      (mem_retainedCompletionWords C u x).1 hxParts.1
    have hyU :=
      (mem_retainedCompletionWords C u y).1 hyParts.1
    exact (hxU e heu).trans (hyU e heu).symm
  · have hev : e ∈ retainedActive C v := by
      by_contra hev
      exact he
        ((mem_commonInactiveRetained C u v e).2
          ⟨heu,hev⟩)
    have hxV :=
      (mem_retainedCompletionWords C v x).1 hxParts.2
    have hyV :=
      (mem_retainedCompletionWords C v y).1 hyParts.2
    exact (hxV e hev).trans (hyV e hev).symm

theorem one_flip_eq_at_of_source_eq_at
    {n : ℕ}
    {x y : Fin n → Bool}
    (c e : Fin n)
    (hxy : x e = y e) :
    flipBoolWordAt x c e =
      flipBoolWordAt y c e := by
  by_cases hec : e = c
  · subst e
    simp [flipBoolWordAt, hxy]
  · simp [flipBoolWordAt, hec, hxy]

theorem two_flip_eq_at_of_source_eq_at
    {n : ℕ}
    {x y : Fin n → Bool}
    (c d e : Fin n)
    (hxy : x e = y e) :
    flipBoolWordAt (flipBoolWordAt x c) d e =
      flipBoolWordAt (flipBoolWordAt y c) d e := by
  apply one_flip_eq_at_of_source_eq_at d e
  exact one_flip_eq_at_of_source_eq_at c e hxy

theorem oneFlip_fullFree_nonempty_capture_is_full
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    (hfull :
      commonInactiveRetained C u v ⊆ retainedInactive C w)
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hbaseW :
      flipBoolWordAt base c ∈ retainedCompletionWords C w) :
    ∀ word,
      word ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v →
      flipBoolWordAt word c ∈ retainedCompletionWords C w := by
  intro word hword
  apply (mem_retainedCompletionWords C w _).2
  intro e heW
  have heNotInactive : e ∉ retainedInactive C w := by
    intro he
    exact (mem_retainedInactive C w e).1 he heW
  have heNotCommon :
      e ∉ commonInactiveRetained C u v := by
    intro he
    exact heNotInactive (hfull he)
  have hbaseEq :
      base e = word e :=
    overlap_words_eq_off_commonInactive
      C hbase hword heNotCommon
  have htransEq :
      flipBoolWordAt base c e =
        flipBoolWordAt word c e :=
    one_flip_eq_at_of_source_eq_at c e hbaseEq
  have hbaseComp :=
    (mem_retainedCompletionWords C w
      (flipBoolWordAt base c)).1 hbaseW
  exact htransEq.symm.trans (hbaseComp e heW)

theorem twoFlip_fullFree_nonempty_capture_is_full
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c d : Fin n}
    (hfull :
      commonInactiveRetained C u v ⊆ retainedInactive C w)
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hbaseW :
      flipBoolWordAt (flipBoolWordAt base c) d ∈
        retainedCompletionWords C w) :
    ∀ word,
      word ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v →
      flipBoolWordAt (flipBoolWordAt word c) d ∈
        retainedCompletionWords C w := by
  intro word hword
  apply (mem_retainedCompletionWords C w _).2
  intro e heW
  have heNotInactive : e ∉ retainedInactive C w := by
    intro he
    exact (mem_retainedInactive C w e).1 he heW
  have heNotCommon :
      e ∉ commonInactiveRetained C u v := by
    intro he
    exact heNotInactive (hfull he)
  have hbaseEq :
      base e = word e :=
    overlap_words_eq_off_commonInactive
      C hbase hword heNotCommon
  have htransEq :
      flipBoolWordAt (flipBoolWordAt base c) d e =
        flipBoolWordAt (flipBoolWordAt word c) d e :=
    two_flip_eq_at_of_source_eq_at c d e hbaseEq
  have hbaseComp :=
    (mem_retainedCompletionWords C w
      (flipBoolWordAt (flipBoolWordAt base c) d)).1 hbaseW
  exact htransEq.symm.trans (hbaseComp e heW)

#print axioms overlap_words_eq_off_commonInactive
#print axioms oneFlip_fullFree_nonempty_capture_is_full
#print axioms twoFlip_fullFree_nonempty_capture_is_full

end OrderedEdgeColoring
end JSP000404Research
