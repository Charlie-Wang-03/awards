import JSP000404Research.ResidualRecolor
import JSP000404Research.WeightedHansel
import Mathlib.Tactic

/-!
# Lightweight retained Boolean completion core

This module contains only the canonical retained bit, the retained partial-code
predicate, and its finite Boolean completion cube.  These primitives are used
by whole-cube local arguments and therefore must not inherit the global
residual-hole repair machinery.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Canonical Boolean bit of a retained old colour. -/
noncomputable def retainedBit
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    V → Fin n → Bool :=
  fun v c => bit C v c.castSucc

/-- A complete retained Boolean word extends the vertex's specified retained
partial code. -/
def RetainedCompletes
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V)
    (word : Fin n → Bool) : Prop :=
  ∀ c, c ∈ retainedActive C v →
    word c = retainedBit C v c

/-- Finite completion cube of the retained partial code. -/
noncomputable def retainedCompletionWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter (RetainedCompletes C v)

@[simp] theorem mem_retainedCompletionWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (word : Fin n → Bool) :
    word ∈ retainedCompletionWords C v ↔
      RetainedCompletes C v word := by
  classical
  simp [retainedCompletionWords]

#print axioms mem_retainedCompletionWords

/-- Free-coordinate completions are equivalent to the retained completion
words of one vertex. -/
noncomputable def retainedCompletionEquivFree
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    FreeCoordinates (retainedActive C v) ≃
      {word : Fin n → Bool //
        word ∈ retainedCompletionWords C v} where
  toFun free := ⟨
    completeWord (retainedBit C) (retainedActive C) v free,
    by
      apply (mem_retainedCompletionWords C v _).2
      intro d hd
      simp [completeWord, hd]⟩
  invFun word :=
    fun d => word.1 d.1
  left_inv free := by
    funext d
    simp [completeWord, d.2]
  right_inv word := by
    apply Subtype.ext
    funext d
    by_cases hd : d ∈ retainedActive C v
    · have hcomp :=
        (mem_retainedCompletionWords C v word.1).1 word.2
      simp [completeWord, hd, hcomp d hd]
    · simp [completeWord, hd]

/-- Exact cardinality of one retained partial-code completion cube. -/
theorem retainedCompletionWords_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    (retainedCompletionWords C v).card =
      2 ^ (n - (retainedActive C v).card) := by
  classical
  have hcard :=
    Fintype.card_congr
      (retainedCompletionEquivFree C v)
  rw [card_freeCoordinates] at hcard
  calc
    (retainedCompletionWords C v).card =
        Fintype.card
          {word : Fin n → Bool //
            word ∈ retainedCompletionWords C v} := by
      symm
      exact Fintype.card_coe _
    _ = 2 ^ (n - (retainedActive C v).card) :=
      hcard.symm

#print axioms retainedCompletionWords_card

end OrderedEdgeColoring
end JSP000404Research
