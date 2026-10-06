import JSP000404Research.ResidualRecolor
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

end OrderedEdgeColoring
end JSP000404Research
