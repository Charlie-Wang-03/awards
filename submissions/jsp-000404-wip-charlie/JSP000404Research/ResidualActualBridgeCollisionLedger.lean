import JSP000404Research.ResidualStrictShellGlobalReserveLedger
import JSP000404Research.ResidualForwardReverseBridgeCapacity
import Mathlib.Tactic

/-!
# Actual forward/reverse image collisions, not hypothetical bridge faces

The previously defined bridge-soft pool B is a union of COMPLETE soft
overlap cubes which COULD support an opposite-direction transport
collision. This is only a geometric POTENTIAL collision pool.

Define the genuine finite collision set I = F intersect R, where F
and R are the exact images of the separately proved globally injective
forward/reverse hard-face transports.

Unlike the candidate bridge pool, I represents genuinely DUPLICATED
destination words. The exact source-mass inclusion-exclusion identity
uses |I|, not |B|, and the disjoint complement B \ I quantifies the
OVERCOUNT in the old candidate-bridge upper bound.

We also prove that all reverse transported words inhabit the actual
strict-rigid LOWER-minus-UPPER shells, allowing a second exact
reverse-image reservation that is disjoint from its remaining slots.

These finite words remain globally COVERED. None of the identities
asserts the missing true-hole or net-surplus payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def actualForwardReverseCollisionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    Finset (Fin n → Bool) :=
  forwardHardTransportSinkWords C ∩
    reverseStrictRigidSinkWords C exponent hexp honeLoss

/-- Genuine forward/reverse cross-map collisions lie in the original
candidate bridge-soft pool; the reverse inclusion is not known. -/
theorem actual_collision_subset_candidate_bridge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    actualForwardReverseCollisionWords C exponent hexp honeLoss ⊆
      forwardReverseBridgeSoftWords C exponent :=
  forward_reverse_sink_inter_subset_bridge_soft C exponent hexp honeLoss

/-- Stronger than reverse images merely being covered: the
CANONICAL reverse flip places each entire strict-rigid source
face inside its corresponding local lower-minus-upper shell. -/
theorem reverse_strict_sink_subset_unused_lower_shells
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    reverseStrictRigidSinkWords C exponent hexp honeLoss ⊆
      netStrictRigidUnusedLowerWords C exponent := by
  classical
  intro word hword
  unfold reverseStrictRigidSinkWords at hword
  obtain ⟨y, _hy, hyword⟩ := Finset.mem_image.mp hword
  let q := strictDescentRigidWordCarrier C exponent y
  have hq : q.1 ∈ netStrictDescentRigidCarriers C exponent := q.2
  let colour := strictDescentRigidPairColor C exponent hexp honeLoss q
  have hcolour :=
    strictDescentRigidPairColor_spec C exponent hexp honeLoss q
  have hwordq :=
    strictDescentRigidWordCarrier_covers C exponent y
  have hswap :
      y.1 ∈ retainedCompletionWords C q.1.2 ∩
        retainedCompletionWords C q.1.1 := by
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hwordq).2,
        (Finset.mem_inter.mp hwordq).1⟩
  have hshell :
      flipCompletionWord colour y.1 ∈
        retainedCompletionWords C q.1.1 \
          retainedCompletionWords C q.1.2 :=
    hard_overlap_cube_flip_mem_upper_only C
      hcolour.1 hcolour.2 hswap
  have himage :
      (strictDescentRigidWordToSingletonOrSoft
          C exponent hexp honeLoss y).1 =
        flipCompletionWord colour y.1 := rfl
  have hsub :=
    strict_rigid_lower_shell_subset_unused C exponent hq
  apply hsub
  rw [← hyword]
  rw [himage]
  exact hshell

/-- Genuine collisions lie INSIDE the actual reverse lower shells,
not just the candidate bridge soft family. -/
theorem actual_collision_subset_strict_shell_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    actualForwardReverseCollisionWords C exponent hexp honeLoss ⊆
      strictShellSoftWords C exponent := by
  intro word hw
  exact (bridge_soft_subset_global_strict_shell_soft C exponent)
    (actual_collision_subset_candidate_bridge
      C exponent hexp honeLoss hw)

/-- Source mass is EXACTLY the size of the union of its images plus
the ACTUAL number of cross-direction collision words, without
adding the entire possible bridge-soft carrier face pool. -/
theorem forward_reverse_source_mass_eq_sink_union_add_actual_collisions
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (transportableHardOverlapCompletionWords C).card +
      (netStrictDescentRigidWords C exponent).card =
        (forwardHardTransportSinkWords C ∪
          reverseStrictRigidSinkWords C exponent hexp honeLoss).card +
          (actualForwardReverseCollisionWords
            C exponent hexp honeLoss).card := by
  classical
  have hf := forwardHardTransportSinkWords_card C
  have hr := reverseStrictRigidSinkWords_card
    C exponent hexp honeLoss
  have hx := Finset.card_union_add_card_inter
    (forwardHardTransportSinkWords C)
    (reverseStrictRigidSinkWords C exponent hexp honeLoss)
  change _ + _ = _ +
    (forwardHardTransportSinkWords C ∩
      reverseStrictRigidSinkWords C exponent hexp honeLoss).card
  omega

/-- Exact-image correction to the previous possible-bridge bound:
only real collisions have to be counted twice. -/
theorem forward_reverse_hard_mass_le_singleton_soft_actual_collision
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (transportableHardOverlapCompletionWords C).card +
      (netStrictDescentRigidWords C exponent).card ≤
        (singletonCompletionWords C).card +
          (softOverlapCompletionWords C).card +
          (actualForwardReverseCollisionWords
            C exponent hexp honeLoss).card := by
  have heq :=
    forward_reverse_source_mass_eq_sink_union_add_actual_collisions
      C exponent hexp honeLoss
  have hsub :=
    forward_reverse_sink_union_subset_singleton_soft
      C exponent hexp honeLoss
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    (singletonCompletionWords C) (softOverlapCompletionWords C)
  omega

/-- The genuinely unused potential bridge words are the exact slack
between the coarse candidate bridge bound and actual cross-map
intersection. They cannot serve as additional duplicate collision
charges. -/
noncomputable def unusedCandidateBridgeWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    Finset (Fin n → Bool) :=
  forwardReverseBridgeSoftWords C exponent \
    actualForwardReverseCollisionWords C exponent hexp honeLoss

/-- Exact number of *unused* candidate collisions is recoverable
from the old possible-bridge overestimate. -/
theorem candidate_bridge_card_eq_actual_plus_unused
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (forwardReverseBridgeSoftWords C exponent).card =
      (actualForwardReverseCollisionWords
        C exponent hexp honeLoss).card +
        (unusedCandidateBridgeWords
          C exponent hexp honeLoss).card := by
  classical
  have hsub :=
    actual_collision_subset_candidate_bridge
      C exponent hexp honeLoss
  have hcard := Finset.card_sdiff_of_subset hsub
  change (unusedCandidateBridgeWords
      C exponent hexp honeLoss).card =
    (forwardReverseBridgeSoftWords C exponent).card -
      (actualForwardReverseCollisionWords
        C exponent hexp honeLoss).card at hcard
  have hle := Finset.card_le_card hsub
  omega

/-- The exact-image strengthening of the former candidate
bridge inequality recovers every unrealized bridge face word. -/
theorem mobile_mass_add_unused_candidates_le_old_bridge_budget
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (transportableHardOverlapCompletionWords C).card +
      (netStrictDescentRigidWords C exponent).card +
      (unusedCandidateBridgeWords
        C exponent hexp honeLoss).card ≤
        (singletonCompletionWords C).card +
          (softOverlapCompletionWords C).card +
          (forwardReverseBridgeSoftWords C exponent).card := by
  have hmob :=
    forward_reverse_hard_mass_le_singleton_soft_actual_collision
      C exponent hexp honeLoss
  have hcard :=
    candidate_bridge_card_eq_actual_plus_unused
      C exponent hexp honeLoss
  omega

/-- The reverse transported strict hard words occupy a literal
subset of U and have EXACT the full reverse hard source mass.
This partitions U into ALREADY-USED reverse sinks and the remaining
lower-shell word capacity. -/
theorem strict_shell_unused_after_reverse_plus_reverse_mass_eq_shell
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netStrictRigidUnusedLowerWords C exponent \
        reverseStrictRigidSinkWords C exponent hexp honeLoss).card +
      (netStrictDescentRigidWords C exponent).card =
        (netStrictRigidUnusedLowerWords C exponent).card := by
  classical
  have hsub :=
    reverse_strict_sink_subset_unused_lower_shells
      C exponent hexp honeLoss
  have hcard := Finset.card_sdiff_of_subset hsub
  have heq := reverseStrictRigidSinkWords_card
    C exponent hexp honeLoss
  omega

#print axioms actual_collision_subset_candidate_bridge
#print axioms reverse_strict_sink_subset_unused_lower_shells
#print axioms actual_collision_subset_strict_shell_soft
#print axioms forward_reverse_source_mass_eq_sink_union_add_actual_collisions
#print axioms forward_reverse_hard_mass_le_singleton_soft_actual_collision
#print axioms candidate_bridge_card_eq_actual_plus_unused
#print axioms mobile_mass_add_unused_candidates_le_old_bridge_budget
#print axioms strict_shell_unused_after_reverse_plus_reverse_mass_eq_shell

end OrderedEdgeColoring
end JSP000404Research
