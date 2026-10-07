import JSP000404Research.ResidualRecolor
import Mathlib.Tactic

/-!
# Lightweight retained-inactive coordinate set

The retained inactive coordinates at a vertex are simply the complement of
its retained active palette inside Fin n.  These elementary definitions and
cardinality facts are used by both blocker-density and translated-overlap
arguments, so they are kept independent of the heavier blocker machinery.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def retainedInactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u : V) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun c => c ∉ retainedActive C u

@[simp] theorem mem_retainedInactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u : V) (c : Fin n) :
    c ∈ retainedInactive C u ↔
      c ∉ retainedActive C u := by
  classical
  simp [retainedInactive]

theorem retainedInactive_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u : V) :
    (retainedInactive C u).card =
      n - (retainedActive C u).card := by
  classical
  have hsub :
      retainedInactive C u =
        (Finset.univ : Finset (Fin n)) \ retainedActive C u := by
    ext c
    simp [retainedInactive]
  rw [hsub, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

#print axioms retainedInactive_card

end OrderedEdgeColoring
end JSP000404Research
