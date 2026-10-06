import JSP000404Research.ResidualBitMerge
import JSP000404Research.RetainedOrientation
import Mathlib.Tactic

/-!
# Lightweight retained-bit orientation facts

The retained canonical bit records whether a retained colour is incoming.
Together with the disjoint incoming/outgoing decomposition of retainedActive,
a false active bit is therefore outgoing.

These tiny facts are isolated here so geometric whole-cube terminals do not
need the heavier same-code repair modules.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem mem_incomingRetained_iff_retainedBit_true_light
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c : Fin n) :
    c ∈ incomingRetained C v ↔
      retainedBit C v c = true := by
  rw [mem_incomingRetained_iff]
  unfold retainedBit
  exact (bit_eq_true_iff C v c.castSucc).symm

theorem mem_outgoingRetained_of_mem_retainedActive_bit_false
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {c : Fin n}
    (hc : c ∈ retainedActive C v)
    (hbit : retainedBit C v c = false) :
    c ∈ outgoingRetained C v := by
  rw [retainedActive_eq_incoming_union_outgoing C v] at hc
  rcases Finset.mem_union.mp hc with hIn | hOut
  · have htrue :=
      (mem_incomingRetained_iff_retainedBit_true_light C v c).1 hIn
    rw [hbit] at htrue
    simp at htrue
  · exact hOut

#print axioms mem_incomingRetained_iff_retainedBit_true_light
#print axioms mem_outgoingRetained_of_mem_retainedActive_bit_false

end OrderedEdgeColoring
end JSP000404Research
