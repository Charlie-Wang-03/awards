import JSP000404Research.ResidualSecondLayerTripleCanonical
import JSP000404Research.ResidualSameCodeOrientation
import Mathlib.Tactic

/-!
# Common-colour bit cut in a saturated Q/T/T/T state

Suppose a saturated Q/T/T/T word is a completion word at s and translated at
x,y,z along pairwise distinct owner coordinates cx,cy,cz, with
retainedActive(s)={cx,cy,cz}.  If a coordinate d is active at all four
vertices and d equals one of cx,cy,cz, then the owner corresponding to d has
the opposite retained bit from the other three vertices.

This is immediate from the common word:
* at s, word d is the retained bit at s;
* at the translated owner whose flip coordinate is d, word d is the negation
  of its retained bit;
* at the other translated owners, d is not flipped, so word d equals their
  retained bit.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem translated_word_bit_eq_retainedBit_of_other_active
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {word : Fin n → Bool}
    {owner d : Fin n}
    (howner : owner ∈ retainedActive C v)
    (hd : d ∈ retainedActive C v)
    (hdo : d ≠ owner)
    (hword :
      word ∈ translatedCompletionWords C v owner) :
    word d = retainedBit C v d := by
  have hbase :
      flipBoolWordAt word owner ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v owner word).1 hword
  have hcomp :=
    (mem_retainedCompletionWords C v
      (flipBoolWordAt word owner)).1 hbase
  have h := hcomp d hd
  rw [flipBoolWordAt_off word hdo] at h
  exact h

theorem translated_word_owner_bit_ne_retainedBit
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {word : Fin n → Bool}
    {owner : Fin n}
    (howner : owner ∈ retainedActive C v)
    (hword :
      word ∈ translatedCompletionWords C v owner) :
    word owner = !(retainedBit C v owner) := by
  have hbase :
      flipBoolWordAt word owner ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v owner word).1 hword
  have hcomp :=
    (mem_retainedCompletionWords C v
      (flipBoolWordAt word owner)).1 hbase
  have h := hcomp owner howner
  rw [flipBoolWordAt_at] at h
  cases hb : retainedBit C v owner <;>
    cases hw : word owner <;>
    simp_all

theorem QTTT_common_colour_eq_cx_bit_cut
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s x y z : V}
    {word : Fin n → Bool}
    {cx cy cz d : Fin n}
    (hcxy : cx ≠ cy)
    (hcxz : cx ≠ cz)
    (hcyz : cy ≠ cz)
    (hsd : d ∈ retainedActive C s)
    (hxd : d ∈ retainedActive C x)
    (hyd : d ∈ retainedActive C y)
    (hzd : d ∈ retainedActive C z)
    (hcxX : cx ∈ retainedActive C x)
    (hcyY : cy ∈ retainedActive C y)
    (hczZ : cz ∈ retainedActive C z)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz)
    (hd : d = cx) :
    retainedBit C x d = !(retainedBit C s d) ∧
    retainedBit C y d = retainedBit C s d ∧
    retainedBit C z d = retainedBit C s d := by
  subst d
  have hsBit :=
    (mem_retainedCompletionWords C s word).1 hsQ cx hsd
  have hxBit :=
    translated_word_owner_bit_ne_retainedBit
      C hcxX hxT
  have hyBit :=
    translated_word_bit_eq_retainedBit_of_other_active
      C hcyY hyd hcxy.symm hyT
  have hzBit :=
    translated_word_bit_eq_retainedBit_of_other_active
      C hczZ hzd hcxz.symm hzT
  constructor
  · rw [← hsBit, hxBit]
    cases h : retainedBit C x cx <;>
      cases hw : word cx <;>
      simp_all
  · constructor
    · exact hyBit.symm.trans hsBit
    · exact hzBit.symm.trans hsBit

theorem QTTT_common_colour_eq_cy_bit_cut
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s x y z : V}
    {word : Fin n → Bool}
    {cx cy cz d : Fin n}
    (hcxy : cx ≠ cy)
    (hcxz : cx ≠ cz)
    (hcyz : cy ≠ cz)
    (hsd : d ∈ retainedActive C s)
    (hxd : d ∈ retainedActive C x)
    (hyd : d ∈ retainedActive C y)
    (hzd : d ∈ retainedActive C z)
    (hcxX : cx ∈ retainedActive C x)
    (hcyY : cy ∈ retainedActive C y)
    (hczZ : cz ∈ retainedActive C z)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz)
    (hd : d = cy) :
    retainedBit C y d = !(retainedBit C s d) ∧
    retainedBit C x d = retainedBit C s d ∧
    retainedBit C z d = retainedBit C s d := by
  subst d
  have hsBit :=
    (mem_retainedCompletionWords C s word).1 hsQ cy hsd
  have hyBit :=
    translated_word_owner_bit_ne_retainedBit
      C hcyY hyT
  have hxBit :=
    translated_word_bit_eq_retainedBit_of_other_active
      C hcxX hxd hcxy hxT
  have hzBit :=
    translated_word_bit_eq_retainedBit_of_other_active
      C hczZ hzd hcyz.symm hzT
  constructor
  · rw [← hsBit, hyBit]
    cases h : retainedBit C y cy <;>
      cases hw : word cy <;>
      simp_all
  · exact ⟨hxBit.symm.trans hsBit,
      hzBit.symm.trans hsBit⟩

theorem QTTT_common_colour_eq_cz_bit_cut
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s x y z : V}
    {word : Fin n → Bool}
    {cx cy cz d : Fin n}
    (hcxy : cx ≠ cy)
    (hcxz : cx ≠ cz)
    (hcyz : cy ≠ cz)
    (hsd : d ∈ retainedActive C s)
    (hxd : d ∈ retainedActive C x)
    (hyd : d ∈ retainedActive C y)
    (hzd : d ∈ retainedActive C z)
    (hcxX : cx ∈ retainedActive C x)
    (hcyY : cy ∈ retainedActive C y)
    (hczZ : cz ∈ retainedActive C z)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz)
    (hd : d = cz) :
    retainedBit C z d = !(retainedBit C s d) ∧
    retainedBit C x d = retainedBit C s d ∧
    retainedBit C y d = retainedBit C s d := by
  subst d
  have hsBit :=
    (mem_retainedCompletionWords C s word).1 hsQ cz hsd
  have hzBit :=
    translated_word_owner_bit_ne_retainedBit
      C hczZ hzT
  have hxBit :=
    translated_word_bit_eq_retainedBit_of_other_active
      C hcxX hxd hcxz hxT
  have hyBit :=
    translated_word_bit_eq_retainedBit_of_other_active
      C hcyY hyd hcyz hyT
  constructor
  · rw [← hsBit, hzBit]
    cases h : retainedBit C z cz <;>
      cases hw : word cz <;>
      simp_all
  · exact ⟨hxBit.symm.trans hsBit,
      hyBit.symm.trans hsBit⟩

#print axioms translated_word_bit_eq_retainedBit_of_other_active
#print axioms translated_word_owner_bit_ne_retainedBit
#print axioms QTTT_common_colour_eq_cx_bit_cut
#print axioms QTTT_common_colour_eq_cy_bit_cut
#print axioms QTTT_common_colour_eq_cz_bit_cut

end OrderedEdgeColoring
end JSP000404Research
