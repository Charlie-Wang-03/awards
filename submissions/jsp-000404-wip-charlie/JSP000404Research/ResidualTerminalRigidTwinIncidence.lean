import JSP000404Research.ResidualTerminalRigidTwinCubeDichotomy
import JSP000404Research.ResidualSameCodeOrientation
import Mathlib.Tactic

/-!
# Terminal twin-rigid edges are fully indistinguishable in retained incidence

Equal-target terminal rigid hard carriers were shown to have exactly
equal retained completion cubes and retained-active supports.
We strengthen this to prove that the LOWER and UPPER endpoints have
the SAME incoming AND outgoing retained-colour supports.

The incoming equality follows from the shared retained Boolean code.
The outgoing equality follows from active = incoming ∪ outgoing and
incoming/outgoing disjointness, not merely from a cardinality count.

Thus terminal rigid carriers split into two independent targets:
* equal target exponent: a full retained-incidence TWIN pair;
* unequal target exponent: strictly decreasing upper exponent.

This structural restriction does NOT imply a new Boolean hole or
discharge the global planar defect payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Same retained Boolean code + equal active support implies
the two endpoints have EQUAL outgoing-retained colour sets. -/
theorem sameRetained_equal_active_outgoing_eq
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hsame : SameRetained C u v)
    (hactive : retainedActive C u = retainedActive C v) :
    outgoingRetained C u = outgoingRetained C v := by
  classical
  have hincoming :
      incomingRetained C u = incomingRetained C v :=
    incomingRetained_eq_of_sameRetained C hsame
  have hdisjU :=
    Finset.disjoint_left.mp
      (incomingRetained_disjoint_outgoingRetained C u)
  have hdisjV :=
    Finset.disjoint_left.mp
      (incomingRetained_disjoint_outgoingRetained C v)
  ext c
  constructor
  · intro hcu
    have hcActiveU : c ∈ retainedActive C u := by
      rw [retainedActive_eq_incoming_union_outgoing C u]
      exact Finset.mem_union_right _ hcu
    have hcActiveV : c ∈ retainedActive C v := by
      simpa only [hactive] using hcActiveU
    rw [retainedActive_eq_incoming_union_outgoing C v] at hcActiveV
    rcases Finset.mem_union.mp hcActiveV with hcvIn | hcvOut
    · have hcuIn : c ∈ incomingRetained C u := by
        simpa only [hincoming] using hcvIn
      exact False.elim (hdisjU hcuIn hcu)
    · exact hcvOut
  · intro hcv
    have hcActiveV : c ∈ retainedActive C v := by
      rw [retainedActive_eq_incoming_union_outgoing C v]
      exact Finset.mem_union_right _ hcv
    have hcActiveU : c ∈ retainedActive C u := by
      simpa only [hactive] using hcActiveV
    rw [retainedActive_eq_incoming_union_outgoing C u] at hcActiveU
    rcases Finset.mem_union.mp hcActiveU with hcuIn | hcuOut
    · have hcvIn : c ∈ incomingRetained C v := by
        simpa only [hincoming] using hcuIn
      exact False.elim (hdisjV hcvIn hcv)
    · exact hcuOut

/-- A genuine terminal rigid carrier is either a FULL retained
incidence twin (same incoming, outgoing and entire completion cubes)
or strictly exponent-descending toward its upper endpoint. -/
theorem netRigidHardCarrier_full_incidence_twin_or_strict_descent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    {p : V × V}
    (hp : p ∈ netRigidHardCarriers C exponent) :
    (exponent p.1 = exponent p.2 ∧
      retainedCompletionWords C p.1 = retainedCompletionWords C p.2 ∧
      incomingRetained C p.1 = incomingRetained C p.2 ∧
      outgoingRetained C p.1 = outgoingRetained C p.2)
    ∨
      exponent p.2 < exponent p.1 := by
  rcases netRigidHardCarrier_twin_cubes_or_strict_target_descent
    C exponent hexp honeLoss hp
    with ⟨heq, hcubes, hactive⟩ | hstrict
  · left
    have hnet := (mem_netRigidHardCarriers C exponent p).1 hp
    have hhard := ((mem_netUnpaidHardCarrierPairs C exponent p).1
      hnet.1).1
    have hr : p ∈ rigidHardOverlapCarrierPairs C :=
      (mem_rigidHardOverlapCarrierPairs C p).2 ⟨hhard,hnet.2⟩
    have hsame : SameRetained C p.1 p.2 :=
      ((mem_hardOverlapCarrierPairs C p).1
        ((mem_rigidHardOverlapCarrierPairs C p).1 hr).1).2
    exact ⟨heq,hcubes,incomingRetained_eq_of_sameRetained C hsame,
      sameRetained_equal_active_outgoing_eq C hsame hactive⟩
  · exact Or.inr hstrict

#print axioms sameRetained_equal_active_outgoing_eq
#print axioms netRigidHardCarrier_full_incidence_twin_or_strict_descent

end OrderedEdgeColoring
end JSP000404Research
