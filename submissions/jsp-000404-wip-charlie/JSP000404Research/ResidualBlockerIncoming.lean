
import JSP000404Research.ResidualDuplicateOrder
import Mathlib.Tactic

/-!
# Blockers move one level upward in the incoming-code Boolean lattice

A retained-neighbour blocker w for a base vertex u at coordinate c has exactly
the retained Boolean code obtained by flipping coordinate c.

If c is retained-inactive at u, then c is not incoming at u, so the c-bit is
false. The blocker therefore has c-bit true while every other retained bit is
unchanged.

Since retained bits are precisely incoming-colour indicators,

  incomingRetained(w) = insert c (incomingRetained(u)).

Thus the monotone blocker construction is not merely order-monotone in the
vertex order; it is also rank-monotone in the Boolean lattice of incoming
retained-colour patterns.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem retainedBit_false_of_retained_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u : V} {c : Fin n}
    (hcu : c ∉ retainedActive C u) :
    retainedBit C u c = false := by
  unfold retainedBit
  apply bit_eq_false_of_not_mem_active
  intro hc
  exact hcu
    ((castSucc_mem_active_iff_mem_retainedActive
      C u c).1 hc)

theorem blocker_retainedBit_true_at
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u w : V} {c : Fin n}
    (hcu : c ∉ retainedActive C u)
    (hblock : RetainedNeighbourBlocker C u c w) :
    retainedBit C w c = true := by
  have huFalse :=
    retainedBit_false_of_retained_inactive C hcu
  have hne := hblock.1
  cases hw : retainedBit C w c <;>
    simp_all

/-- Exact incoming-pattern update under an inactive-coordinate blocker. -/
theorem incomingRetained_eq_insert_of_blocker
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u w : V} {c : Fin n}
    (hcu : c ∉ retainedActive C u)
    (hblock : RetainedNeighbourBlocker C u c w) :
    incomingRetained C w =
      insert c (incomingRetained C u) := by
  classical
  ext d
  by_cases hdc : d = c
  · subst d
    have hwTrue :=
      blocker_retainedBit_true_at C hcu hblock
    rw [mem_incomingRetained_iff_retainedBit_true]
    simp [hwTrue]
  · have hbit :
        retainedBit C w d = retainedBit C u d :=
      hblock.2 d hdc
    rw [mem_incomingRetained_iff_retainedBit_true,
        mem_incomingRetained_iff_retainedBit_true]
    simp [hdc, hbit]

/-- The incoming-pattern rank increases by exactly one. -/
theorem incomingRetained_card_blocker
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u w : V} {c : Fin n}
    (hcu : c ∉ retainedActive C u)
    (hblock : RetainedNeighbourBlocker C u c w) :
    (incomingRetained C w).card =
      (incomingRetained C u).card + 1 := by
  rw [incomingRetained_eq_insert_of_blocker
      C hcu hblock]
  have hcNotIn :
      c ∉ incomingRetained C u := by
    intro hc
    rw [retainedActive_eq_incoming_union_outgoing C u] at hcu
    exact hcu (Finset.mem_union_left _ hc)
  rw [Finset.card_insert_of_not_mem hcNotIn]

#print axioms retainedBit_false_of_retained_inactive
#print axioms blocker_retainedBit_true_at
#print axioms incomingRetained_eq_insert_of_blocker
#print axioms incomingRetained_card_blocker

end OrderedEdgeColoring
end JSP000404Research
