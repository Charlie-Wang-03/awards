import JSP000404Research.ResidualTerminalTwinNetPaymentReduction
import Mathlib.Tactic

/-!
# Forward / reverse global transport: cross-collisions are SOFT

The forward transportable hard-face map leaves its images in the
UPPER endpoint's retained completion cube. The reverse strict-rigid
map leaves its images in the LOWER endpoint's retained cube.

Hard carrier endpoint MATCHING shows these endpoints are distinct
even when the two carriers are from different movable classes.
Thus a forward/reverse collision is covered by TWO different
centres, hence cannot be a singleton. As it is already certified
singleton OR SOFT, it must be SOFT.

This is a concrete cross-map collision theorem; it does not claim
that collisions are absent, or that the target is a true hole.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem forward_reverse_sink_collision_is_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C})
    (y : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent})
    (hcollision :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1) :
    (transportableHardWordToSingletonOrSoft C x).1 ∈
      softOverlapCompletionWords C := by
  classical
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let w := (transportableHardWordToSingletonOrSoft C x).1
  have hpinfo := (mem_transportableHardOverlapCarrierPairs C p.1).1 p.2
  have hqinfo := (mem_netStrictDescentRigidCarriers C exponent q.1).1 q.2
  have hqnet := (mem_netRigidHardCarriers C exponent q.1).1 hqinfo.1
  have hqhard := ((mem_netUnpaidHardCarrierPairs C exponent q.1).1
    hqnet.1).1
  have hneq : p.1.2 ≠ q.1.1 := by
    intro heq
    have hpq : p.1 = q.1 :=
      hard_carrier_shared_endpoint_implies_same_pair
        C hpinfo.1 hqhard (Or.inr (Or.inr (Or.inl heq)))
    have htrans : HasOutgoingHardTransport C q.1.1 q.1.2 := by
      simpa only [hpq] using hpinfo.2
    exact hqnet.2 htrans
  have hpword : w ∈ retainedCompletionWords C p.1.2 :=
    transportableHardWordToSingletonOrSoft_mem_upper C x
  have hqword : w ∈ retainedCompletionWords C q.1.1 := by
    change (transportableHardWordToSingletonOrSoft C x).1 ∈
      retainedCompletionWords C q.1.1
    rw [hcollision]
    exact strictDescentRigidWordToSingletonOrSoft_mem_lower
      C exponent hexp honeLoss y
  have hsub :
      ({p.1.2, q.1.1} : Finset V) ⊆ completionFibre C w := by
    intro z hz
    have hz' : z = p.1.2 ∨ z = q.1.1 := by
      simpa using hz
    rcases hz' with rfl | rfl
    · exact (mem_completionFibre C w _).2 hpword
    · exact (mem_completionFibre C w _).2 hqword
  have htwo : 2 ≤ (completionFibre C w).card := by
    have hcard : ({p.1.2, q.1.1} : Finset V).card = 2 := by
      simp [hneq]
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hout := (transportableHardWordToSingletonOrSoft C x).2
  rcases Finset.mem_union.mp hout with hsingle | hsoft
  · have hcard := (mem_singletonCompletionWords C w).1 hsingle
    omega
  · exact hsoft

#print axioms forward_reverse_sink_collision_is_soft

end OrderedEdgeColoring
end JSP000404Research
