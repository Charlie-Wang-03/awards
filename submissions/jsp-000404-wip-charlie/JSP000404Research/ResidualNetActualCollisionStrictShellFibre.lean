import JSP000404Research.ResidualIncomparableBridgeLowerExponent
import JSP000404Research.ResidualStrictShellSoftMassLedger
import Mathlib.Tactic

/-!
# Unique strict-rigid lower-shell ownership of ACTUAL net collisions

The previous target-relative half-face estimate summed over BRIDGES.
Different bridges can share their strict-rigid lower endpoint b, so
this was not a non-reusing reservation of the lower dyadic budget.

Here we construct a stronger exact accounting object: partition
the ACTUAL collision intersection (net unpaid forward hard sinks
intersect reverse strict-rigid sinks) by each strict-rigid lower
shell Q_b \ Q_z.

Distinct rigid lower shells are pairwise disjoint, by the already
kernel-certified strict-hard carrier matching. Thus the actual
collision set, not just the potential bridge pool, decomposes into
a FINITE DISJOINT UNION indexed by strict-rigid carrier q.

Each local collision class is a subset of the SOFT part of its own
strict lower shell, disjoint from its singleton reserve. The local
inequality deducts those singleton words before using the exact
strict target descent gap; no duplicated lower target or hole credit.

Everything in these shells is COVERED, not a true Boolean hole.
This correct ledger remains a stepping stone, NOT a proof of
the final six-source geometric defect payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def netActualCollisionStrictShellWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (q : V × V) : Finset (Fin n → Bool) :=
  netActualForwardReverseCollisionWords C exponent hexp honeLoss ∩
    (retainedCompletionWords C q.1 \
      retainedCompletionWords C q.2)

/-- Every actual NET collision lies in one of the already-certified
unused strict-rigid lower completion slots; no actual intersection
can occupy a singleton sink or a genuine Boolean hole. -/
theorem net_actual_collision_subset_unused_strict_lower_words
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netActualForwardReverseCollisionWords C exponent hexp honeLoss ⊆
      netStrictRigidUnusedLowerWords C exponent := by
  intro word hw
  have hfiltered :=
    net_actual_collision_subset_incomparable_bridge_words
      C exponent hexp honeLoss hw
  have hbridge :=
    incomparable_bridge_soft_words_subset_candidate C exponent hfiltered
  exact bridge_soft_subset_unused_strict_lower_words C exponent hbridge

/-- EXACT union of real collisions among strict-rigid lower shells.
The result rules out counting one collision twice at two distinct
strict-rigid lower endpoints. -/
theorem net_actual_collision_eq_union_strict_shell_fibres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netActualForwardReverseCollisionWords C exponent hexp honeLoss =
      (netStrictDescentRigidCarriers C exponent).biUnion
        (netActualCollisionStrictShellWords C exponent hexp honeLoss) := by
  classical
  ext word
  constructor
  · intro hw
    have hu :=
      net_actual_collision_subset_unused_strict_lower_words
        C exponent hexp honeLoss hw
    rw [unused_strict_lower_words_eq_union_shells] at hu
    obtain ⟨q, hq, hshell⟩ := Finset.mem_biUnion.mp hu
    exact Finset.mem_biUnion.mpr
      ⟨q, hq, Finset.mem_inter.mpr ⟨hw, hshell⟩⟩
  · intro hw
    obtain ⟨q, _hq, hword⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_inter.mp hword).1

/-- A single ACTUAL collision belongs to exactly ONE strict-rigid
lower shell; the cardinality of all collisions is the sum of LOCAL
collision cardinalities, WITHOUT lower-target reuse. -/
theorem net_actual_collision_card_eq_strict_shell_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netActualForwardReverseCollisionWords
      C exponent hexp honeLoss).card =
      ∑ q ∈ netStrictDescentRigidCarriers C exponent,
        (netActualCollisionStrictShellWords
          C exponent hexp honeLoss q).card := by
  classical
  rw [net_actual_collision_eq_union_strict_shell_fibres]
  apply Finset.card_biUnion
  intro q hq r hr hqr
  change Disjoint
    (netActualCollisionStrictShellWords
      C exponent hexp honeLoss q)
    (netActualCollisionStrictShellWords
      C exponent hexp honeLoss r)
  apply Finset.disjoint_left.mpr
  intro word hwq hwr
  have hdisj :=
    strict_rigid_lower_shells_pairwiseDisjoint
      C exponent hq hr hqr
  exact (Finset.disjoint_left.mp hdisj)
    (Finset.mem_inter.mp hwq).2
    (Finset.mem_inter.mp hwr).2

/-- ACTUAL collisions in q are a subset of its SOFT shell, rather
than the total shell or a fresh independent pool. -/
theorem net_actual_collision_strict_shell_subset_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (q : V × V) :
    netActualCollisionStrictShellWords C exponent hexp honeLoss q ⊆
      ((retainedCompletionWords C q.1 \
          retainedCompletionWords C q.2) ∩
        softOverlapCompletionWords C) := by
  intro word hw
  have hcollision := (Finset.mem_inter.mp hw).1
  have hshell := (Finset.mem_inter.mp hw).2
  have hbridge := incomparable_bridge_soft_words_subset_candidate
    C exponent
    (net_actual_collision_subset_incomparable_bridge_words
      C exponent hexp honeLoss hcollision)
  have hsoft :=
    forwardReverseBridgeSoftWords_subset_soft C exponent hbridge
  exact Finset.mem_inter.mpr ⟨hshell, hsoft⟩

/-- Strict q's own shell singleton reserve MUST be deducted before
assigning any available covered soft capacity to ACTUAL collisions
in that same q-shell. This is a genuine per-carrier budget bound
in which no other rigid lower target is used. -/
theorem net_actual_collision_local_plus_singletons_le_target_gap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    {q : V × V}
    (hq : q ∈ netStrictDescentRigidCarriers C exponent) :
    (netActualCollisionStrictShellWords
      C exponent hexp honeLoss q).card +
      (((retainedCompletionWords C q.1 \
          retainedCompletionWords C q.2) ∩
        singletonCompletionWords C).card) ≤
      2 ^ exponent q.1 - 2 ^ exponent q.2 := by
  have hsoft :=
    Finset.card_le_card
      (net_actual_collision_strict_shell_subset_soft
        C exponent hexp honeLoss q)
  have hsoftMass :=
    strict_shell_soft_card_eq_outgoing_dyadic_sum C exponent hq
  have htotal :=
    strict_shell_singleton_add_outgoing_soft_mass_eq_target_gap
      C exponent hexp honeLoss hq
  omega

#print axioms net_actual_collision_subset_unused_strict_lower_words
#print axioms net_actual_collision_eq_union_strict_shell_fibres
#print axioms net_actual_collision_card_eq_strict_shell_sum
#print axioms net_actual_collision_strict_shell_subset_soft
#print axioms net_actual_collision_local_plus_singletons_le_target_gap

end OrderedEdgeColoring
end JSP000404Research
