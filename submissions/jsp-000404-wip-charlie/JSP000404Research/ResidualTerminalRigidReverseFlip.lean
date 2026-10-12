import JSP000404Research.ResidualHardCarrierVertexMatching
import JSP000404Research.ResidualHardOverlapCubeSoftRouting
import Mathlib.Tactic

/-!
# Strict-descending terminal rigid hard carriers admit a REVERSE safe flip

A no-outgoing-transport rigid hard pair (a,v) always satisfies
retainedActive(a) ⊆ retainedActive(v).

When both endpoint projected budgets are saturated AND the upper
exponent is strictly smaller, this containment is STRICT.
Because the SAME retained Boolean code forces equal incoming colours,
there must be a retained colour OUTGOING at v yet INACTIVE at a.

That is precisely a reverse-direction analogue of the forward hard
transport. It flips the entire doubly-covered upper face Q_v
into Q_a \ Q_v, where the images are necessarily singleton-
covered or SOFT-overlapped, never hard-overlapped.

Crucial caution: these destinations are STILL COVERED, not true
Boolean holes. Global injection and global PAYMENT require
additional arguments. This file formalizes the local reverse
certificate without an unproved geometric hypothesis.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- No outgoing hard transport + strict reverse projected-free
dimension gap yields a colour outgoing at UPPER and inactive at LOWER. -/
theorem rigid_strict_projectedFree_has_reverse_safe_colour
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V}
    (hsame : SameRetained C a v)
    (hno : ¬ HasOutgoingHardTransport C a v)
    (hfree : projectedFree C v < projectedFree C a) :
    ∃ c : Fin n,
      c ∈ outgoingRetained C v ∧
      c ∉ retainedActive C a := by
  classical
  have hactiveSub :=
    hard_no_transport_retainedActive_subset C hsame hno
  have hactA : (retainedActive C a).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C a)
  have hactV : (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  have hcard : (retainedActive C a).card <
      (retainedActive C v).card := by
    unfold projectedFree at hfree
    omega
  have hnotSubset :
      ¬ retainedActive C v ⊆ retainedActive C a := by
    intro hsubset
    have hc := Finset.card_le_card hsubset
    omega
  have hsome :
      ∃ c : Fin n,
        c ∈ retainedActive C v ∧ c ∉ retainedActive C a := by
    by_contra hnone
    have hsub : retainedActive C v ⊆ retainedActive C a := by
      intro c hc
      by_contra hnot
      exact hnone ⟨c,hc,hnot⟩
    exact hnotSubset hsub
  obtain ⟨c,hcv,hnot⟩ := hsome
  have hin := incomingRetained_eq_of_sameRetained C hsame
  rw [retainedActive_eq_incoming_union_outgoing C v] at hcv
  rcases Finset.mem_union.mp hcv with hi | ho
  · have hia : c ∈ incomingRetained C a := by
      rw [hin]
      exact hi
    have hca : c ∈ retainedActive C a := by
      rw [retainedActive_eq_incoming_union_outgoing C a]
      exact Finset.mem_union_left _ hia
    exact False.elim (hnot hca)
  · exact ⟨c,ho,hnot⟩

/-- For EVERY strictly-descending terminal rigid carrier, the
reverse safe colour is guaranteed by saturation and the verified
one-layer active-card budget; no new global Hall assumption. -/
theorem netRigidHardCarrier_strict_descent_has_reverse_safe_colour
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    {p : V × V}
    (hp : p ∈ netRigidHardCarriers C exponent)
    (hstrict : exponent p.2 < exponent p.1) :
    ∃ c : Fin n,
      c ∈ outgoingRetained C p.2 ∧
      c ∉ retainedActive C p.1 := by
  have hnet := (mem_netRigidHardCarriers C exponent p).1 hp
  have hhp := (mem_netUnpaidHardCarrierPairs C exponent p).1 hnet.1
  have hrig : p ∈ rigidHardOverlapCarrierPairs C :=
    (mem_rigidHardOverlapCarrierPairs C p).2 ⟨hhp.1,hnet.2⟩
  have hsat :=
    terminal_rigid_carrier_both_saturated_without_word
      C exponent hrig hhp.2.1 hhp.2.2.1 hhp.2.2.2
      (netRigidHardCarriers_endpoint_budgets_of_oneLayer
        C exponent hexp honeLoss p hp).1
      (netRigidHardCarriers_endpoint_budgets_of_oneLayer
        C exponent hexp honeLoss p hp).2
  have hfree : projectedFree C p.2 < projectedFree C p.1 := by
    omega
  have hsame := ((mem_hardOverlapCarrierPairs C p).1 hhp.1).2
  exact rigid_strict_projectedFree_has_reverse_safe_colour
    C hsame hnet.2 hfree

/-- Every Boolean word of an actual strictly-descending
terminal rigid face has a one-bit REVERSE flip which exits the
upper cube, remains in the lower cube, and lands in the union
of singleton and SOFT-covered completion words. -/
theorem netRigidHardCarrier_strict_descent_flip_to_lower_singleton_or_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    {p : V × V} {word : Fin n → Bool}
    (hp : p ∈ netRigidHardCarriers C exponent)
    (hstrict : exponent p.2 < exponent p.1)
    (hword : word ∈ carrierOverlapWords C p) :
    ∃ c : Fin n,
      c ∈ outgoingRetained C p.2 ∧
      c ∉ retainedActive C p.1 ∧
      flipCompletionWord c word ∈
        retainedCompletionWords C p.1 \
          retainedCompletionWords C p.2 ∧
      flipCompletionWord c word ∈
        singletonCompletionWords C ∪
          softOverlapCompletionWords C := by
  classical
  obtain ⟨c,hout,hinactive⟩ :=
    netRigidHardCarrier_strict_descent_has_reverse_safe_colour
      C exponent hexp honeLoss hp hstrict
  have hhp := (mem_netUnpaidHardCarrierPairs C exponent p).1
    ((mem_netRigidHardCarriers C exponent p).1 hp).1
  have hsame := ((mem_hardOverlapCarrierPairs C p).1 hhp.1).2
  have horder : p.1 < p.2 :=
    ((mem_residualCarrierPairs C p.1 p.2).1
      ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1 hhp.1).1).1).1
  have hswapped : word ∈
      retainedCompletionWords C p.2 ∩
        retainedCompletionWords C p.1 := by
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hword).2,
       (Finset.mem_inter.mp hword).1⟩
  have hsameSwap : SameRetained C p.2 p.1 :=
    fun d => (hsame d).symm
  refine ⟨c,hout,hinactive,?_,?_⟩
  · exact hard_overlap_cube_flip_mem_upper_only
      C hout hinactive hswapped
  · exact hard_overlap_full_face_flip_singleton_or_soft
      C (ne_of_gt horder) hsameSwap
        hout hinactive hswapped

#print axioms rigid_strict_projectedFree_has_reverse_safe_colour
#print axioms netRigidHardCarrier_strict_descent_has_reverse_safe_colour
#print axioms netRigidHardCarrier_strict_descent_flip_to_lower_singleton_or_soft

end OrderedEdgeColoring
end JSP000404Research
