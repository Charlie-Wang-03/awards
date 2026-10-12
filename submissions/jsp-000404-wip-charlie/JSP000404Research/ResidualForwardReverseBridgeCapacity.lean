import JSP000404Research.ResidualForwardReverseBridgeSoftFaces
import Mathlib.Tactic

/-!
# Sharpen joint mobile-hard capacity to the exact possible SOFT BRIDGE pool

Earlier, forward and reverse hard transports were shown to be
individually injective and their cross-collisions SOFT.
This yielded
  fullForwardMass + reverseStrictRigidMass
    <= singletonMass + 2*allSoftMass.

The NEW uniquely-owned bridge-face theorem shows every cross-map
collision lies within a canonical (often smaller) Finset of soft
words joining the lower endpoint of a strict-descending rigid hard
carrier to the upper endpoint of an outgoing-transportable hard
carrier.

Exact finite-set inclusion-exclusion now yields
  fullForwardMass + reverseStrictRigidMass
    <= singletonMass + allSoftMass + bridgeSoftMass.

The extra bridgeSoftMass is a REAL, explicit, finite and geometrically
characterised potential collision mass, not an arbitrary duplicate
copy of all soft words. We neither assert it is empty nor count
covered sink words as true holes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem forward_reverse_sink_inter_subset_bridge_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    forwardHardTransportSinkWords C ∩
        reverseStrictRigidSinkWords C exponent hexp honeLoss ⊆
      forwardReverseBridgeSoftWords C exponent := by
  classical
  intro word hw
  have hf := (Finset.mem_inter.mp hw).1
  have hr := (Finset.mem_inter.mp hw).2
  unfold forwardHardTransportSinkWords at hf
  unfold reverseStrictRigidSinkWords at hr
  obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hf
  obtain ⟨y,_,hy⟩ := Finset.mem_image.mp hr
  have hcollision :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1 := hx.trans hy.symm
  have hbridge :=
    forward_reverse_sink_collision_in_bridge_soft_words
      C exponent hexp honeLoss x y hcollision
  simpa only [hx] using hbridge

theorem forward_reverse_hard_mass_le_singleton_soft_bridge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (transportableHardOverlapCompletionWords C).card +
      (netStrictDescentRigidWords C exponent).card ≤
        (singletonCompletionWords C).card +
          (softOverlapCompletionWords C).card +
          (forwardReverseBridgeSoftWords C exponent).card := by
  classical
  let F := forwardHardTransportSinkWords C
  let R := reverseStrictRigidSinkWords C exponent hexp honeLoss
  let S := singletonCompletionWords C
  let T := softOverlapCompletionWords C
  let B := forwardReverseBridgeSoftWords C exponent
  have hf : F.card =
      (transportableHardOverlapCompletionWords C).card :=
    forwardHardTransportSinkWords_card C
  have hr : R.card =
      (netStrictDescentRigidWords C exponent).card :=
    reverseStrictRigidSinkWords_card C exponent hexp honeLoss
  have hsubset : F ∪ R ⊆ S ∪ T :=
    forward_reverse_sink_union_subset_singleton_soft
      C exponent hexp honeLoss
  have hbridge : F ∩ R ⊆ B :=
    forward_reverse_sink_inter_subset_bridge_soft
      C exponent hexp honeLoss
  have hunion : (F ∪ R).card ≤ (S ∪ T).card :=
    Finset.card_le_card hsubset
  have hinter : (F ∩ R).card ≤ B.card :=
    Finset.card_le_card hbridge
  have hsum : (S ∪ T).card ≤ S.card + T.card :=
    Finset.card_union_le S T
  have hexact := Finset.card_union_add_card_inter F R
  have hS : S.card = (singletonCompletionWords C).card := rfl
  have hT : T.card = (softOverlapCompletionWords C).card := rfl
  have hB : B.card = (forwardReverseBridgeSoftWords C exponent).card := rfl
  omega

/-- Version for the ACTUALLY unpaid forward hard faces, rather than
all outward-transportable hard overlap faces including paid words. -/
theorem net_forward_reverse_hard_mass_le_singleton_soft_bridge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤
        (singletonCompletionWords C).card +
          (softOverlapCompletionWords C).card +
          (forwardReverseBridgeSoftWords C exponent).card := by
  have hsub := Finset.card_le_card
    (netTransportableHardWords_subset_transportable C exponent)
  have hb := forward_reverse_hard_mass_le_singleton_soft_bridge
    C exponent hexp honeLoss
  omega

/-- Genuine remaining hard mass now has the smaller, explicit
bridged-soft collision pool plus the EXACT true-twin dyadic debt. -/
theorem remaining_hard_mass_le_singleton_soft_bridge_add_twin
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (remainingUnpaidHardAfterMixedRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card +
        (forwardReverseBridgeSoftWords C exponent).card +
        (∑ p ∈ netTwinRigidCarriers C exponent,
          2 ^ exponent p.2) := by
  have hsplit := remainingUnpaidHard_card_eq_transport_strict_twin
    C exponent hexp honeLoss
  have htwin := netTwinRigidWords_card_eq_dyadic_target_sum
    C exponent hexp honeLoss
  have hmobile := net_forward_reverse_hard_mass_le_singleton_soft_bridge
    C exponent hexp honeLoss
  omega

/-- When the well-defined finite soft bridge obstruction is empty,
forward and reverse hard transports are JOINTLY injective into a
single common singleton-or-soft sink set. This conditional theorem
does not claim bridge emptiness for planar AngleCap configurations. -/
theorem forward_reverse_hard_mass_le_singleton_soft_of_no_bridge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    (hno : forwardReverseBridgeSoftWords C exponent = ∅) :
    (transportableHardOverlapCompletionWords C).card +
      (netStrictDescentRigidWords C exponent).card ≤
        (singletonCompletionWords C).card +
          (softOverlapCompletionWords C).card := by
  have hbound := forward_reverse_hard_mass_le_singleton_soft_bridge
    C exponent hexp honeLoss
  simp only [hno, Finset.card_empty, add_zero] at hbound
  exact hbound

#print axioms forward_reverse_sink_inter_subset_bridge_soft
#print axioms forward_reverse_hard_mass_le_singleton_soft_bridge
#print axioms net_forward_reverse_hard_mass_le_singleton_soft_bridge
#print axioms remaining_hard_mass_le_singleton_soft_bridge_add_twin
#print axioms forward_reverse_hard_mass_le_singleton_soft_of_no_bridge

end OrderedEdgeColoring
end JSP000404Research
