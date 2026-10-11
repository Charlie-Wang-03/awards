import JSP000404Research.DirectionDataThreePointG1HallRefutation
import JSP000404Research.ResidualHardRigidMassAccounting
import Mathlib.Tactic

/-!
# Actual DirectionData countermodel to universal outgoing hard-face transport

The previously audited three-point DirectionData profile satisfies ALL
of the abstract DirectionData axioms and the stated LocalDirectionCycle
exponents. Its two high-band vertices 0<1 have the SAME retained code
and EXACTLY the SAME retained active set {1} in Fin 2.

Their residual edge is hard and its nonempty completion intersection
is nested (indeed the two cubes are equal). Therefore no outward
retained colour at 0 can be inactive at 1.

This KERNEL-CHECKED counterexample proves that the newly isolated
HasHardOverlapOutgoingTransport hypothesis is NOT a consequence
of abstract DirectionData alone. Any proof of JSP-000404 MUST either
use genuinely additional planar geometric structure or pay rigid
hard-overlap faces without this transport.

As in the earlier G1 audit, no geometric planar realization is
asserted. Failure of this optional transport mechanism is NOT a
counterexample to the original JSP-000404 dyadic capacity.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

private noncomputable def rigidExampleC :
    OrderedEdgeColoring (Fin 3) 3 :=
  standardResidualColoring candidateThreePointData 2 (by norm_num)

theorem rigidExample_sameRetained_zero_one :
    SameRetained rigidExampleC 0 1 := by
  intro c
  have h0 := (exampleB_retained_bits_both_false c).1
  have h1 := (exampleB_retained_bits_both_false c).2
  change retainedBit rigidExampleC 0 c = false at h0
  change retainedBit rigidExampleC 1 c = false at h1
  exact h0.trans h1.symm

theorem rigidExample_retainedActive_zero_eq_one :
    retainedActive rigidExampleC 0 =
      retainedActive rigidExampleC 1 := by
  have h := candidateThreePoint_retainedActive_01
  change
    retainedActive rigidExampleC 0 =
        ({(1 : Fin 2)} : Finset (Fin 2)) ∧
    retainedActive rigidExampleC 1 =
        ({(1 : Fin 2)} : Finset (Fin 2)) at h
  exact h.1.trans h.2.symm

theorem rigidExample_residual_zero_one :
    IsResidual rigidExampleC 0 1 := by
  exact exampleB_residual_zero_one

theorem rigidExample_no_outgoing_transport :
    ¬ HasOutgoingHardTransport rigidExampleC 0 1 := by
  rintro ⟨c, hout, hinactive⟩
  have ha : c ∈ retainedActive rigidExampleC 0 := by
    rw [retainedActive_eq_incoming_union_outgoing rigidExampleC 0]
    exact Finset.mem_union_right _ hout
  have hv : c ∈ retainedActive rigidExampleC 1 := by
    rw [← rigidExample_retainedActive_zero_eq_one]
    exact ha
  exact hinactive hv

/-- A truly hard residual overlap carrier, not just a same-code pair. -/
theorem rigidExample_hard_overlap_carrier :
    ((0 : Fin 3), (1 : Fin 3)) ∈
      hardOverlapCarrierPairs rigidExampleC := by
  have hsame := rigidExample_sameRetained_zero_one
  have hoverlap := retained_base_mem_both_completionWords
    rigidExampleC hsame
  apply (mem_hardOverlapCarrierPairs rigidExampleC (0,1)).2
  constructor
  · apply (mem_overlapCarrierPairs rigidExampleC (0,1)).2
    constructor
    · apply (mem_residualCarrierPairs rigidExampleC 0 1).2
      exact ⟨by decide, rigidExample_residual_zero_one⟩
    · exact ⟨(fun d => retainedBit rigidExampleC 0 d),
        hoverlap⟩
  · exact hsame

/-- The universal full-face outgoing/inactive transport assumption
is FALSE even in an explicit, axiomatically valid DirectionData model. -/
theorem abstract_directionData_refutes_universal_hard_transport :
    ¬ HasHardOverlapOutgoingTransport rigidExampleC := by
  intro hglobal
  have h := hglobal (0,1) rigidExample_hard_overlap_carrier
  exact rigidExample_no_outgoing_transport h

/-- The obstruction is not a zero-mass artifact: a real residual
hard overlap carrier is RIGID in the exact partition. -/
theorem rigidExample_rigid_overlap_carrier :
    ((0 : Fin 3), (1 : Fin 3)) ∈
      rigidHardOverlapCarrierPairs rigidExampleC := by
  exact (mem_rigidHardOverlapCarrierPairs rigidExampleC (0,1)).2
    ⟨rigidExample_hard_overlap_carrier,
     rigidExample_no_outgoing_transport⟩

/-- This concrete rigid example has a FULL nested upper cube. -/
theorem rigidExample_upper_cube_nested :
    retainedCompletionWords rigidExampleC 1 ⊆
      retainedCompletionWords rigidExampleC 0 :=
  hard_no_transport_upper_cube_subset_lower
    rigidExampleC rigidExample_sameRetained_zero_one
      rigidExample_no_outgoing_transport

#print axioms rigidExample_sameRetained_zero_one
#print axioms rigidExample_no_outgoing_transport
#print axioms abstract_directionData_refutes_universal_hard_transport
#print axioms rigidExample_rigid_overlap_carrier

end DirectionData
end JSP000404Research
