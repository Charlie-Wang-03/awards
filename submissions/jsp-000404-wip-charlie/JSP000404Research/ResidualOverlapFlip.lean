
import JSP000404Research.ResidualOverlapDimension
import JSP000404Research.ResidualUnsafeEdgeBudget
import Mathlib.Tactic

/-!
# Safe-coordinate transport of projected overlap words

Let word lie in Q_u inter Q_v and let c be a safe retained colour for the
residual pair, meaning c is not incoming at u and not outgoing at v.

Compatibility of the common word implies that c cannot be retained-active at
both endpoints.

Flipping coordinate c therefore has exactly three possibilities.

* c active only at u:
    flip(word,c) lies in Q_v but not Q_u.
* c active only at v:
    flip(word,c) lies in Q_u but not Q_v.
* c inactive at both:
    flip(word,c) remains in Q_u inter Q_v.

Thus every safe overlap coordinate either transports a duplicated word into a
single-covered region or moves inside the common-inactive overlap subcube.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def flipRetainedWord
    {n : ℕ}
    (word : Fin n → Bool)
    (c : Fin n) :
    Fin n → Bool :=
  fun d => if d = c then !(word d) else word d

theorem flipRetainedWord_at_ne
    {n : ℕ}
    (word : Fin n → Bool)
    (c : Fin n) :
    flipRetainedWord word c c ≠ word c := by
  cases h : word c <;>
    simp [flipRetainedWord, h]

theorem flipRetainedWord_off
    {n : ℕ}
    (word : Fin n → Bool)
    {c d : Fin n}
    (hdc : d ≠ c) :
    flipRetainedWord word c d = word d := by
  simp [flipRetainedWord, hdc]

/-- On an overlap pair, a safe coordinate cannot be active at both endpoints. -/
theorem safe_overlap_not_active_both
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {word : Fin n → Bool}
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    {c : Fin n}
    (hsafe : c ∉ residualForbidden C u v) :
    ¬ (c ∈ retainedActive C u ∧
       c ∈ retainedActive C v) := by
  intro hboth
  have hnotInU : c ∉ incomingRetained C u := by
    intro hc
    exact hsafe (Finset.mem_union_left _ hc)
  have hnotOutV : c ∉ outgoingRetained C v := by
    intro hc
    exact hsafe (Finset.mem_union_right _ hc)
  have hOutU : c ∈ outgoingRetained C u := by
    rw [retainedActive_eq_incoming_union_outgoing C u] at hboth
    rcases Finset.mem_union.mp hboth.1 with hIn | hOut
    · exact False.elim (hnotInU hIn)
    · exact hOut
  have hInV : c ∈ incomingRetained C v := by
    rw [retainedActive_eq_incoming_union_outgoing C v] at hboth
    rcases Finset.mem_union.mp hboth.2 with hIn | hOut
    · exact hIn
    · exact False.elim (hnotOutV hOut)
  have huComp :=
    (mem_retainedCompletionWords C u word).1 hu
  have hvComp :=
    (mem_retainedCompletionWords C v word).1 hv
  have hbitUFalse : retainedBit C u c = false := by
    unfold retainedBit
    apply bit_eq_false_iff.mpr
    intro hex
    exact hnotInU
      ((mem_incomingRetained_iff C u c).2 hex)
  have hbitVTrue :
      retainedBit C v c = true :=
    (mem_incomingRetained_iff_retainedBit_true C v c).1 hInV
  have hwU := huComp c hboth.1
  have hwV := hvComp c hboth.2
  rw [hbitUFalse] at hwU
  rw [hbitVTrue] at hwV
  rw [hwU] at hwV
  decide

/-- Safe coordinate active only at u transports overlap to Q_v \ Q_u. -/
theorem flip_overlap_to_right_single
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {word : Fin n → Bool}
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    {c : Fin n}
    (hsafe : c ∉ residualForbidden C u v)
    (hcu : c ∈ retainedActive C u) :
    flipRetainedWord word c ∈ retainedCompletionWords C v ∧
      flipRetainedWord word c ∉ retainedCompletionWords C u := by
  have hcv : c ∉ retainedActive C v := by
    intro h
    exact safe_overlap_not_active_both
      C hu hv hsafe ⟨hcu,h⟩
  constructor
  · apply (mem_retainedCompletionWords C v _).2
    intro d hdv
    have hdc : d ≠ c := by
      intro h
      subst d
      exact hcv hdv
    rw [flipRetainedWord_off word hdc]
    exact (mem_retainedCompletionWords C v word).1 hv d hdv
  · intro hflipU
    have hcomp :=
      (mem_retainedCompletionWords C u
        (flipRetainedWord word c)).1 hflipU
    have hbase :=
      (mem_retainedCompletionWords C u word).1 hu
    have h1 := hcomp c hcu
    have h2 := hbase c hcu
    exact flipRetainedWord_at_ne word c
      (h1.trans h2.symm)

/-- Safe coordinate active only at v transports overlap to Q_u \ Q_v. -/
theorem flip_overlap_to_left_single
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {word : Fin n → Bool}
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    {c : Fin n}
    (hsafe : c ∉ residualForbidden C u v)
    (hcv : c ∈ retainedActive C v) :
    flipRetainedWord word c ∈ retainedCompletionWords C u ∧
      flipRetainedWord word c ∉ retainedCompletionWords C v := by
  have hcu : c ∉ retainedActive C u := by
    intro h
    exact safe_overlap_not_active_both
      C hu hv hsafe ⟨h,hcv⟩
  constructor
  · apply (mem_retainedCompletionWords C u _).2
    intro d hdu
    have hdc : d ≠ c := by
      intro h
      subst d
      exact hcu hdu
    rw [flipRetainedWord_off word hdc]
    exact (mem_retainedCompletionWords C u word).1 hu d hdu
  · intro hflipV
    have hcomp :=
      (mem_retainedCompletionWords C v
        (flipRetainedWord word c)).1 hflipV
    have hbase :=
      (mem_retainedCompletionWords C v word).1 hv
    have h1 := hcomp c hcv
    have h2 := hbase c hcv
    exact flipRetainedWord_at_ne word c
      (h1.trans h2.symm)

/-- Common-inactive safe coordinate moves inside the overlap cube. -/
theorem flip_overlap_stays_overlap_of_commonInactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {word : Fin n → Bool}
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    {c : Fin n}
    (hcu : c ∉ retainedActive C u)
    (hcv : c ∉ retainedActive C v) :
    flipRetainedWord word c ∈
      retainedCompletionWords C u ∩
        retainedCompletionWords C v := by
  rw [Finset.mem_inter]
  constructor
  · apply (mem_retainedCompletionWords C u _).2
    intro d hdu
    have hdc : d ≠ c := by
      intro h
      subst d
      exact hcu hdu
    rw [flipRetainedWord_off word hdc]
    exact (mem_retainedCompletionWords C u word).1 hu d hdu
  · apply (mem_retainedCompletionWords C v _).2
    intro d hdv
    have hdc : d ≠ c := by
      intro h
      subst d
      exact hcv hdv
    rw [flipRetainedWord_off word hdc]
    exact (mem_retainedCompletionWords C v word).1 hv d hdv

/-- Complete safe-coordinate trichotomy on an overlap pair. -/
theorem safe_overlap_flip_trichotomy
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {word : Fin n → Bool}
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    {c : Fin n}
    (hsafe : c ∉ residualForbidden C u v) :
    (c ∈ retainedActive C u ∧
      flipRetainedWord word c ∈ retainedCompletionWords C v ∧
      flipRetainedWord word c ∉ retainedCompletionWords C u)
    ∨
    (c ∈ retainedActive C v ∧
      flipRetainedWord word c ∈ retainedCompletionWords C u ∧
      flipRetainedWord word c ∉ retainedCompletionWords C v)
    ∨
    (c ∉ retainedActive C u ∧
      c ∉ retainedActive C v ∧
      flipRetainedWord word c ∈
        retainedCompletionWords C u ∩
          retainedCompletionWords C v) := by
  by_cases hcu : c ∈ retainedActive C u
  · left
    exact ⟨hcu,
      (flip_overlap_to_right_single C hu hv hsafe hcu).1,
      (flip_overlap_to_right_single C hu hv hsafe hcu).2⟩
  · by_cases hcv : c ∈ retainedActive C v
    · right
      left
      exact ⟨hcv,
        (flip_overlap_to_left_single C hu hv hsafe hcv).1,
        (flip_overlap_to_left_single C hu hv hsafe hcv).2⟩
    · right
      right
      exact ⟨hcu,hcv,
        flip_overlap_stays_overlap_of_commonInactive
          C hu hv hcu hcv⟩

#print axioms safe_overlap_not_active_both
#print axioms flip_overlap_to_right_single
#print axioms flip_overlap_to_left_single
#print axioms safe_overlap_flip_trichotomy

end OrderedEdgeColoring
end JSP000404Research
