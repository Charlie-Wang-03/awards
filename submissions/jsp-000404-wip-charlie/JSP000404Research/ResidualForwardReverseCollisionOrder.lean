import JSP000404Research.ResidualForwardReverseJointSoftMultiplicity
import Mathlib.Tactic

/-!
# Order restriction for collisions of opposite-direction global transports

If an increasing residual edge a<v has upper completion cube Q_v,
and some OTHER centre b has a completion word in common with Q_v,
then b MUST lie below v. Indeed the other order v<b would force
a forbidden increasing monochromatic two-edge path a<v<b.

In particular, a collision of our certified full-face forward
and reverse transports produces an additional residual bridge
  reverseLower < forwardUpper
  IsResidual C reverseLower forwardUpper.
The earlier collision theorem shows this bridge word is SOFT.

Unlike a conjectural Hall payment, these are unconditional
kernel-certified constraints on all genuinely colliding images.
The bridge does not itself imply a Boolean hole.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem residual_upper_cube_overlap_forces_backward_bridge
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v b : V} {word : Fin n → Bool}
    (hav : a < v)
    (hresAV : IsResidual C a v)
    (hvb : v ≠ b)
    (hvword : word ∈ retainedCompletionWords C v)
    (hbword : word ∈ retainedCompletionWords C b) :
    b < v ∧ IsResidual C b v := by
  rcases retainedCompletion_overlap_forces_residual C hvb hvword hbword
    with ⟨hvbLt,hresVB⟩ | ⟨hbvLt,hresBV⟩
  · exact False.elim
      (no_two_residual_on_path C hav hvbLt hresAV hresVB)
  · exact ⟨hbvLt,hresBV⟩

/-- Any actual collision of opposite-direction global hard-face
transports forces a residual bridge in ONE orientation: the
reverse rigid carrier's lower endpoint precedes the forward
transportable carrier's upper endpoint. -/
theorem forward_reverse_sink_collision_forces_backward_residual_bridge
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
    let p := transportableWordCarrier C x
    let q := strictDescentRigidWordCarrier C exponent y
    q.1.1 < p.1.2 ∧ IsResidual C q.1.1 p.1.2 := by
  classical
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
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
  have hpRes := transportableWordCarrier_residual C x
  have hpword :
      (transportableHardWordToSingletonOrSoft C x).1 ∈
        retainedCompletionWords C p.1.2 :=
    transportableHardWordToSingletonOrSoft_mem_upper C x
  have hqword :
      (transportableHardWordToSingletonOrSoft C x).1 ∈
        retainedCompletionWords C q.1.1 := by
    rw [hcollision]
    exact strictDescentRigidWordToSingletonOrSoft_mem_lower
      C exponent hexp honeLoss y
  exact residual_upper_cube_overlap_forces_backward_bridge
    C hpRes.1 hpRes.2 hneq hpword hqword

#print axioms residual_upper_cube_overlap_forces_backward_bridge
#print axioms forward_reverse_sink_collision_forces_backward_residual_bridge

end OrderedEdgeColoring
end JSP000404Research
